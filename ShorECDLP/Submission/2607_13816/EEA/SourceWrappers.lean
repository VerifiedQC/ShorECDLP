import ShorECDLP.Submission.«2607_13816».EEA.SourceSchedules
import ShorECDLP.Submission.«2607_13816».Arithmetic.SourceAdapters
import ShorECDLP.Submission.«2607_13816».EEA.AdaptiveWrapper
namespace ShorECDLP.Paper2607_13816
open Quantum
def controlledConstMinusSource (input dirty : List Wire) (modulus : List Bool)
    (q c r t : Wire) : CorrectionProgram :=
  .unitary [.ordinary (controlledComplement input q)]
    ((controlledGidneyAddConstSource input dirty
      ((List.range input.length).map (Nat.testBit 1)) q c r t).seq
      (controlledGidneyAddConstSource input dirty modulus q c r t))
theorem controlledConstMinusSource_erase (input dirty : List Wire) (modulus : List Bool)
    (q c r t : Wire) :
    (controlledConstMinusSource input dirty modulus q c r t).erase=controlledConstMinus input dirty modulus q c r t := by
  simp [controlledConstMinusSource,controlledConstMinus,CorrectionProgram.erase,
    correctionBlockErase,CorrectionFragment.erase,CorrectionProgram.erase_seq,controlledGidneyAddConstSource_erase]
theorem controlledConstMinusSource_events (input dirty : List Wire) (modulus : List Bool)
    (q c r t : Wire) (hi : 0 < input.length) (hd : dirty.length=input.length-1)
    (hm : modulus.length=input.length) :
    (controlledConstMinusSource input dirty modulus q c r t).events=
      2*(input.length-1)+(if modulus.all (fun k => !k) then 0 else 2*(input.length-1)) := by
  have hone : (((List.range input.length).map (Nat.testBit 1)).all (fun k => !k))=false := by
    obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : input.length≠0)
    rw [hn,List.range_succ_eq_map]
    simp
  simp [controlledConstMinusSource,CorrectionProgram.events,correctionBlockEvents,CorrectionFragment.events,
    CorrectionProgram.events_seq,controlledGidneyAddConstSource_events input dirty ((List.range input.length).map (Nat.testBit 1)) q c r t hi hd (by simp),
    controlledGidneyAddConstSource_events input dirty modulus q c r t hi hd hm,hone]
def eeaCenterSource (input dirty : List Wire) (modulus : List Bool) (p : Nat)
    (c r t iter : Wire) : CorrectionProgram :=
  (gidneyCompareGESource input dirty (p/2+1) c r t iter).seq
    (controlledConstMinusSource input (dirty.take (input.length-1)) modulus iter c r t)
def eeaUncenterSource (input dirty : List Wire) (modulus : List Bool) (p : Nat)
    (c r t iter : Wire) : CorrectionProgram :=
  (controlledConstMinusSource input (dirty.take (input.length-1)) modulus iter c r t).seq
    (gidneyCompareGESource input dirty (p/2+1) c r t iter)
theorem eeaCenterSource_erase (input dirty : List Wire) (modulus : List Bool) (p : Nat)
    (c r t iter : Wire) : (eeaCenterSource input dirty modulus p c r t iter).erase=eeaCenter input dirty modulus p c r t iter := by
  simp [eeaCenterSource,eeaCenter,CorrectionProgram.erase_seq,gidneyCompareGESource_erase,controlledConstMinusSource_erase]
theorem eeaUncenterSource_erase (input dirty : List Wire) (modulus : List Bool) (p : Nat)
    (c r t iter : Wire) : (eeaUncenterSource input dirty modulus p c r t iter).erase=eeaUncenter input dirty modulus p c r t iter := by
  simp [eeaUncenterSource,eeaUncenter,CorrectionProgram.erase_seq,gidneyCompareGESource_erase,controlledConstMinusSource_erase]
theorem eeaCenterSource_events (input dirty : List Wire) (modulus : List Bool) (p : Nat)
    (c r t iter : Wire) (hi : 0 < input.length) (hd : dirty.length=input.length)
    (hm : modulus.length=input.length) :
    (eeaCenterSource input dirty modulus p c r t iter).events=
      (if p/2+1=0 ∨ 2^input.length≤p/2+1 then 0 else 2*input.length)+
        (2*(input.length-1)+(if modulus.all (fun k => !k) then 0 else 2*(input.length-1))) := by
  rw [eeaCenterSource,CorrectionProgram.events_seq,gidneyCompareGESource_events _ _ _ _ _ _ _ hd,
    controlledConstMinusSource_events _ _ _ _ _ _ _ hi (by simp [hd]) hm]
theorem eeaUncenterSource_events (input dirty : List Wire) (modulus : List Bool) (p : Nat)
    (c r t iter : Wire) (hi : 0 < input.length) (hd : dirty.length=input.length)
    (hm : modulus.length=input.length) :
    (eeaUncenterSource input dirty modulus p c r t iter).events=
      (eeaCenterSource input dirty modulus p c r t iter).events := by
  rw [eeaCenterSource_events _ _ _ _ _ _ _ _ hi hd hm,eeaUncenterSource,CorrectionProgram.events_seq,
    gidneyCompareGESource_events _ _ _ _ _ _ _ hd,
    controlledConstMinusSource_events _ _ _ _ _ _ _ hi (by simp [hd]) hm]
  omega
def eeaParityCorrectionSource (input dirty : List Wire) (modulus : List Bool)
    (c r t iter : Wire) : CorrectionProgram :=
  .unitary [.ordinary [.X iter]] ((controlledConstMinusSource input dirty modulus iter c r t).seq
    (.unitary [.ordinary [.X iter]] .done))
theorem eeaParityCorrectionSource_erase (input dirty : List Wire) (modulus : List Bool)
    (c r t iter : Wire) : (eeaParityCorrectionSource input dirty modulus c r t iter).erase=
      eeaParityCorrection input dirty modulus c r t iter := by
  simp [eeaParityCorrectionSource,eeaParityCorrection,CorrectionProgram.erase,correctionBlockErase,
    CorrectionFragment.erase,CorrectionProgram.erase_seq,controlledConstMinusSource_erase]
theorem eeaParityCorrectionSource_events (input dirty : List Wire) (modulus : List Bool)
    (c r t iter : Wire) (hi : 0 < input.length) (hd : dirty.length=input.length-1)
    (hm : modulus.length=input.length) :
    (eeaParityCorrectionSource input dirty modulus c r t iter).events=
      2*(input.length-1)+(if modulus.all (fun k => !k) then 0 else 2*(input.length-1)) := by
  simp [eeaParityCorrectionSource,CorrectionProgram.events,correctionBlockEvents,CorrectionFragment.events,
    CorrectionProgram.events_seq,controlledConstMinusSource_events _ _ _ _ _ _ _ hi hd hm]
end ShorECDLP.Paper2607_13816
namespace ShorECDLP.Paper2607_13816
open Quantum
def eeaPreprocessSource : CorrectionProgram :=
  CorrectionProgram.unitary [.ordinary workRegistersPrepare]
    ((eeaCenterSource (List.range' 266 256).reverse (List.range' 4 256)
      (constantBits 256 (2 ^ 256 - 2 ^ 32 - 977)) (2 ^ 256 - 2 ^ 32 - 977)
      560 561 562 2).seq (CorrectionProgram.unitary [.ordinary eeaLengthSetup] .done))
theorem eeaPreprocessSource_erase : eeaPreprocessSource.erase=eeaPreprocess := by
  simp [eeaPreprocessSource,eeaPreprocess,eeaCenterSource_erase,CorrectionProgram.erase_seq,CorrectionProgram.erase,correctionBlockErase,CorrectionFragment.erase]
def eeaUnpreprocessSource : CorrectionProgram :=
  CorrectionProgram.unitary [.ordinary eeaLengthUndo]
    ((eeaUncenterSource (List.range' 266 256).reverse (List.range' 4 256)
      (constantBits 256 (2 ^ 256 - 2 ^ 32 - 977)) (2 ^ 256 - 2 ^ 32 - 977)
      560 561 562 2).seq (CorrectionProgram.unitary [.ordinary workRegistersRestore] .done))
theorem eeaUnpreprocessSource_erase : eeaUnpreprocessSource.erase=eeaUnpreprocess := by
  simp [eeaUnpreprocessSource,eeaUnpreprocess,eeaUncenterSource_erase,CorrectionProgram.erase_seq,CorrectionProgram.erase,correctionBlockErase,CorrectionFragment.erase]
def secp256k1EEAParitySource : CorrectionProgram :=
  eeaParityCorrectionSource (List.range' 263 256) (List.range' 4 255) secp256k1ModulusBits 560 561 562 2
theorem secp256k1EEAParitySource_erase : secp256k1EEAParitySource.erase=secp256k1EEAParityCorrection := by
  simp [secp256k1EEAParitySource,secp256k1EEAParityCorrection,eeaParityCorrectionSource_erase]
def secp256k1EEAForwardWrapperSource : CorrectionProgram :=
  ((((eeaPreprocessSource.seq (secp256k1EEAForwardSource)).seq
    (CorrectionProgram.unitary [.ordinary (canonicalWork2Rotation ++ terminalEpochCompression)] .done)).seq
    secp256k1EEAParitySource).seq (CorrectionProgram.unitary [.ordinary terminalWork1Clear] .done))
theorem secp256k1EEAForwardWrapperSource_erase : secp256k1EEAForwardWrapperSource.erase=secp256k1EEAForwardWrapper := by
  simp [secp256k1EEAForwardWrapperSource,secp256k1EEAForwardWrapper,eeaPreprocessSource_erase,secp256k1EEAForwardSource_certificate.1,secp256k1EEAParitySource_erase,CorrectionProgram.erase_seq,CorrectionProgram.erase,correctionBlockErase,CorrectionFragment.erase]
def secp256k1EEAReversePostprocessingSource : CorrectionProgram :=
  ((CorrectionProgram.unitary [.ordinary terminalWork1Clear] .done).seq secp256k1EEAParitySource).seq
    (CorrectionProgram.unitary [.ordinary (terminalEpochCompression ++ canonicalWork2InverseRotation)] .done)
theorem secp256k1EEAReversePostprocessingSource_erase : secp256k1EEAReversePostprocessingSource.erase=secp256k1EEAReversePostprocessing := by
  simp [secp256k1EEAReversePostprocessingSource,secp256k1EEAReversePostprocessing,secp256k1EEAParitySource_erase,CorrectionProgram.erase_seq,CorrectionProgram.erase,correctionBlockErase,CorrectionFragment.erase]
def secp256k1EEAReverseWrapperSource : CorrectionProgram :=
  (secp256k1EEAReversePostprocessingSource.seq
    (secp256k1EEAReverseSource)).seq eeaUnpreprocessSource
theorem secp256k1EEAReverseWrapperSource_erase : secp256k1EEAReverseWrapperSource.erase=secp256k1EEAReverseWrapper := by
  simp [secp256k1EEAReverseWrapperSource,secp256k1EEAReverseWrapper,secp256k1EEAReverseSource_certificate.1,secp256k1EEAReversePostprocessingSource_erase,eeaUnpreprocessSource_erase,CorrectionProgram.erase_seq]
end ShorECDLP.Paper2607_13816
namespace ShorECDLP.Paper2607_13816
open Quantum
private theorem sourceCenterThreshold :
    ¬((2^256-2^32-977)/2+1=0 ∨ 2^256≤(2^256-2^32-977)/2+1) := by decide +kernel
private theorem sourceCenterBits :
    (constantBits 256 (2^256-2^32-977)).all (fun k => !k)=false := by decide +kernel
private theorem sourceParityBits : secp256k1ModulusBits.all (fun k => !k)=false := by decide +kernel
private theorem sourceCenter256 (input dirty : List Wire) (c r t iter : Wire)
    (hi : input.length=256) (hd : dirty.length=256) :
    (eeaCenterSource input dirty (constantBits 256 (2^256-2^32-977)) (2^256-2^32-977) c r t iter).events=1532 := by
  rw [eeaCenterSource_events _ _ _ _ _ _ _ _ (by omega) (by omega) (by simp [hi])]
  simp only [hi,sourceCenterThreshold,sourceCenterBits,if_false,Bool.false_eq_true]
private theorem sourceUncenter256 (input dirty : List Wire) (c r t iter : Wire)
    (hi : input.length=256) (hd : dirty.length=256) :
    (eeaUncenterSource input dirty (constantBits 256 (2^256-2^32-977)) (2^256-2^32-977) c r t iter).events=1532 := by
  rw [eeaUncenterSource_events _ _ _ _ _ _ _ _ (by omega) (by omega) (by simp [hi])]
  exact sourceCenter256 _ _ _ _ _ _ hi hd
private theorem sourceUnitaryEvents (fs : List CorrectionFragment) (p : CorrectionProgram) :
    (CorrectionProgram.unitary fs p).events=correctionBlockEvents fs+p.events := rfl
theorem eeaPreprocessSource_events : eeaPreprocessSource.events=1532 := by
  rw [eeaPreprocessSource,sourceUnitaryEvents,CorrectionProgram.events_seq,
    sourceCenter256 _ _ _ _ _ _ (by simp) (by simp)]
  rfl
theorem eeaUnpreprocessSource_events : eeaUnpreprocessSource.events=1532 := by
  rw [eeaUnpreprocessSource,sourceUnitaryEvents,CorrectionProgram.events_seq,
    sourceUncenter256 _ _ _ _ _ _ (by simp) (by simp)]
  rfl
theorem secp256k1EEAParitySource_events : secp256k1EEAParitySource.events=1020 := by
  rw [secp256k1EEAParitySource,eeaParityCorrectionSource_events _ _ _ _ _ _ _ (by simp) (by simp)
    (by simp [secp256k1ModulusBits])]
  simp only [List.length_range',sourceParityBits,Bool.false_eq_true,if_false]
/-- All source corrections belong to the same concrete forward wrapper. -/
theorem secp256k1EEAForwardWrapperSource_certificate :
    secp256k1EEAForwardWrapperSource.erase=secp256k1EEAForwardWrapper ∧
      secp256k1EEAForwardWrapperSource.events=5281384 := by
  refine ⟨secp256k1EEAForwardWrapperSource_erase,?_⟩
  simp [secp256k1EEAForwardWrapperSource,CorrectionProgram.events_seq,
    eeaPreprocessSource_events,secp256k1EEAForwardSource_certificate.2,secp256k1EEAParitySource_events,
    CorrectionProgram.events,correctionBlockEvents,CorrectionFragment.events]
theorem secp256k1EEAReversePostprocessingSource_events : secp256k1EEAReversePostprocessingSource.events=1020 := by
  simp [secp256k1EEAReversePostprocessingSource,CorrectionProgram.events_seq,secp256k1EEAParitySource_events,
    CorrectionProgram.events,correctionBlockEvents,CorrectionFragment.events]
/-- Source corrections of the explicit reverse wrapper, including reverse preprocessing. -/
theorem secp256k1EEAReverseWrapperSource_certificate :
    secp256k1EEAReverseWrapperSource.erase=secp256k1EEAReverseWrapper ∧
      secp256k1EEAReverseWrapperSource.events=5281384 := by
  refine ⟨secp256k1EEAReverseWrapperSource_erase,?_⟩
  simp [secp256k1EEAReverseWrapperSource,CorrectionProgram.events_seq,
    secp256k1EEAReversePostprocessingSource_events,secp256k1EEAReverseSource_certificate.2,eeaUnpreprocessSource_events]
end ShorECDLP.Paper2607_13816
