import ShorECDLP.Submission.«2607_13816».Arithmetic.SourceRelabel
import ShorECDLP.Submission.«2607_13816».EEA.SourceWrappers
import ShorECDLP.Submission.«2607_13816».Arithmetic.SourceLoops
import ShorECDLP.Submission.«2607_13816».Arithmetic.ZeroAllowed
namespace ShorECDLP.Paper2607_13816
open Quantum
def secp256k1EEAForwardInDataBankSource : CorrectionProgram :=
  secp256k1EEAForwardWrapperSource.relabel eeaWorkspaceExchange
theorem secp256k1EEAForwardInDataBankSource_certificate :
    secp256k1EEAForwardInDataBankSource.erase=secp256k1EEAForwardInDataBank ∧ secp256k1EEAForwardInDataBankSource.events=5281384 := by
  constructor
  · rw [secp256k1EEAForwardInDataBankSource,CorrectionProgram.erase_relabel,secp256k1EEAForwardWrapperSource_certificate.1]
    rfl
  · rw [secp256k1EEAForwardInDataBankSource,CorrectionProgram.events_relabel,secp256k1EEAForwardWrapperSource_certificate.2]
def secp256k1EEAReverseInDataBankSource : CorrectionProgram :=
  secp256k1EEAReverseWrapperSource.relabel eeaWorkspaceExchange
theorem secp256k1EEAReverseInDataBankSource_certificate :
    secp256k1EEAReverseInDataBankSource.erase=secp256k1EEAReverseInDataBank ∧ secp256k1EEAReverseInDataBankSource.events=5281384 := by
  constructor
  · rw [secp256k1EEAReverseInDataBankSource,CorrectionProgram.erase_relabel,secp256k1EEAReverseWrapperSource_certificate.1]
    rfl
  · rw [secp256k1EEAReverseInDataBankSource,CorrectionProgram.events_relabel,secp256k1EEAReverseWrapperSource_certificate.2]
private theorem figSourceThreshold : ¬(ShorECDLP.p=0 ∨ 2^256≤ShorECDLP.p) := by decide +kernel
private theorem figSourceReduction : secp256k1ReductionConstantBits.all (fun k => !k)=false := by decide +kernel
private theorem figSourceModulus : (constantBits 256 ShorECDLP.p).all (fun k => !k)=false := by decide +kernel
def fig15MultiplyToWorkSource : CorrectionProgram :=
  hornerMulSource (List.range' 263 256) (List.range' 580 256) (List.range' 7 256)
    secp256k1ReductionConstantBits ShorECDLP.p 558 560 561 559
theorem fig15MultiplyToWorkSource_certificate :
    fig15MultiplyToWorkSource.erase=fig15MultiplyToWork ∧ fig15MultiplyToWorkSource.events=522242 := by
  constructor
  · exact hornerMulSource_erase _ _ _ _ _ _ _ _ _
  · have h := hornerMulSource_events (List.range' 263 256) (List.range' 580 256) 7 (List.range' 8 255)
      secp256k1ReductionConstantBits ShorECDLP.p 558 560 561 559 (by simp) (by decide +kernel)
    change fig15MultiplyToWorkSource.events=_ at h
    simpa only [List.length_range',List.length_cons,figSourceThreshold,if_false,figSourceReduction,Bool.false_eq_true] using h
def fig15MultiplyToDataSource : CorrectionProgram :=
  hornerMulSource (List.range' 263 256) (List.range' 7 256) (List.range' 580 256)
    secp256k1ReductionConstantBits ShorECDLP.p 558 560 561 559
theorem fig15MultiplyToDataSource_certificate :
    fig15MultiplyToDataSource.erase=fig15MultiplyToData ∧ fig15MultiplyToDataSource.events=522242 := by
  constructor
  · exact hornerMulSource_erase _ _ _ _ _ _ _ _ _
  · have h := hornerMulSource_events (List.range' 263 256) (List.range' 7 256) 580 (List.range' 581 255)
      secp256k1ReductionConstantBits ShorECDLP.p 558 560 561 559 (by simp) (by decide +kernel)
    change fig15MultiplyToDataSource.events=_ at h
    simpa only [List.length_range',List.length_cons,figSourceThreshold,if_false,figSourceReduction,Bool.false_eq_true] using h
def fig15MultiplyToDataInverseSource : CorrectionProgram :=
  hornerMulInverseSource (List.range' 263 256) (List.range' 7 256) (List.range' 580 256)
    (constantBits 256 ShorECDLP.p) ShorECDLP.p 558 560 561 559
theorem fig15MultiplyToDataInverseSource_certificate :
    fig15MultiplyToDataInverseSource.erase=fig15MultiplyToDataInverse ∧ fig15MultiplyToDataInverseSource.events=522242 := by
  constructor
  · exact hornerMulInverseSource_erase _ _ _ _ _ _ _ _ _
  · have h := hornerMulInverseSource_events (List.range' 263 256) (List.range' 7 256) 580 (List.range' 581 255)
      (constantBits 256 ShorECDLP.p) ShorECDLP.p 558 560 561 559 (by simp) (by decide +kernel)
    change fig15MultiplyToDataInverseSource.events=_ at h
    simpa only [List.length_range',List.length_cons,figSourceThreshold,if_false,figSourceModulus,Bool.false_eq_true] using h
end ShorECDLP.Paper2607_13816
namespace ShorECDLP.Paper2607_13816
open Quantum
private theorem sourceOrdinaryErase (g : Circuit) : correctionBlockErase [.ordinary g]=g := by
  simp [correctionBlockErase,CorrectionFragment.erase]
private theorem sourceOrdinaryEvents (g : Circuit) : correctionBlockEvents [.ordinary g]=0 := rfl
def fig15DivisionAfterResetSource (outcomes : List Bool) : CorrectionProgram :=
  (((secp256k1EEAReverseInDataBankSource.seq fig15MultiplyToDataSource).seq
    (.unitary (registerZFragments (List.range' 580 256) outcomes) .done)).seq
      fig15MultiplyToDataInverseSource).seq (.unitary [.ordinary fig15SwapOutput] .done)
def fig15MultiplicationAfterResetSource (outcomes : List Bool) : CorrectionProgram :=
  ((((secp256k1EEAForwardInDataBankSource.seq fig15MultiplyToDataSource).seq
    (.unitary (registerZFragments (List.range' 580 256) outcomes) .done)).seq
      fig15MultiplyToDataInverseSource).seq secp256k1EEAReverseInDataBankSource).seq
        (.unitary [.ordinary fig15SwapOutput] .done)
theorem fig15DivisionAfterResetSource_erase (bs : List Bool) :
    (fig15DivisionAfterResetSource bs).erase=fig15DivisionAfterReset bs := by
  simp [fig15DivisionAfterResetSource,fig15DivisionAfterReset,CorrectionProgram.erase_seq,
    secp256k1EEAReverseInDataBankSource_certificate.1,fig15MultiplyToDataSource_certificate.1,
    fig15MultiplyToDataInverseSource_certificate.1,CorrectionProgram.erase,registerZFragments_erase,
    sourceOrdinaryErase]
theorem fig15MultiplicationAfterResetSource_erase (bs : List Bool) :
    (fig15MultiplicationAfterResetSource bs).erase=fig15MultiplicationAfterReset bs := by
  simp [fig15MultiplicationAfterResetSource,fig15MultiplicationAfterReset,CorrectionProgram.erase_seq,
    secp256k1EEAForwardInDataBankSource_certificate.1,secp256k1EEAReverseInDataBankSource_certificate.1,
    fig15MultiplyToDataSource_certificate.1,fig15MultiplyToDataInverseSource_certificate.1,
    CorrectionProgram.erase,registerZFragments_erase,sourceOrdinaryErase]
theorem fig15DivisionAfterResetSource_events (bs : List Bool) (hb : bs.length=256) :
    (fig15DivisionAfterResetSource bs).events=6325868+bs.count true := by
  simp [fig15DivisionAfterResetSource,CorrectionProgram.events_seq,
    secp256k1EEAReverseInDataBankSource_certificate.2,fig15MultiplyToDataSource_certificate.2,
    fig15MultiplyToDataInverseSource_certificate.2,CorrectionProgram.events,
    registerZFragments_events (List.range' 580 256) bs (by simpa using hb),
    sourceOrdinaryEvents]
  omega
theorem fig15MultiplicationAfterResetSource_events (bs : List Bool) (hb : bs.length=256) :
    (fig15MultiplicationAfterResetSource bs).events=11607252+bs.count true := by
  simp [fig15MultiplicationAfterResetSource,CorrectionProgram.events_seq,
    secp256k1EEAForwardInDataBankSource_certificate.2,secp256k1EEAReverseInDataBankSource_certificate.2,
    fig15MultiplyToDataSource_certificate.2,fig15MultiplyToDataInverseSource_certificate.2,
    CorrectionProgram.events,registerZFragments_events (List.range' 580 256) bs (by simpa using hb),
    sourceOrdinaryEvents]
  omega
def secp256k1InPlaceDivisionSource : CorrectionProgram :=
  (secp256k1EEAForwardWrapperSource.seq fig15MultiplyToWorkSource).seq
    (correctionResetThen (List.range' 580 256) fig15DivisionAfterResetSource)
def secp256k1InPlaceMultiplicationSource : CorrectionProgram :=
  fig15MultiplyToWorkSource.seq
    (correctionResetThen (List.range' 580 256) fig15MultiplicationAfterResetSource)
/-- Retain every reset outcome across the intervening calls in the literal division stream. -/
theorem secp256k1InPlaceDivisionSource_certificate :
    secp256k1InPlaceDivisionSource.erase=secp256k1InPlaceDivision ∧
      secp256k1InPlaceDivisionSource.events=12129750 := by
  constructor
  · simp only [secp256k1InPlaceDivisionSource,secp256k1InPlaceDivision,CorrectionProgram.erase_seq,
      secp256k1EEAForwardWrapperSource_certificate.1,fig15MultiplyToWorkSource_certificate.1,
      correctionResetThen_erase,fig15DivisionAfterResetSource_erase]
  · rw [secp256k1InPlaceDivisionSource,CorrectionProgram.events_seq,CorrectionProgram.events_seq,
      secp256k1EEAForwardWrapperSource_certificate.2,fig15MultiplyToWorkSource_certificate.2,
      correctionResetThen_events _ _ 6325868 1 (by
        intro bs hb
        simpa using fig15DivisionAfterResetSource_events bs (by simpa using hb))]
    simp only [List.length_range']
/-- The multiplication stream retains the same selected corrections in its own source order. -/
theorem secp256k1InPlaceMultiplicationSource_certificate :
    secp256k1InPlaceMultiplicationSource.erase=secp256k1InPlaceMultiplication ∧
      secp256k1InPlaceMultiplicationSource.events=12129750 := by
  constructor
  · simp only [secp256k1InPlaceMultiplicationSource,secp256k1InPlaceMultiplication,CorrectionProgram.erase_seq,
      fig15MultiplyToWorkSource_certificate.1,correctionResetThen_erase,fig15MultiplicationAfterResetSource_erase]
  · rw [secp256k1InPlaceMultiplicationSource,CorrectionProgram.events_seq,fig15MultiplyToWorkSource_certificate.2,
      correctionResetThen_events _ _ 11607252 1 (by
        intro bs hb
        simpa using fig15MultiplicationAfterResetSource_events bs (by simpa using hb))]
    simp only [List.length_range']
end ShorECDLP.Paper2607_13816
namespace ShorECDLP.Paper2607_13816
open Quantum
def secp256k1ZeroAllowedDivisionSource : CorrectionProgram :=
  ((CorrectionProgram.unitary [.ordinary fig15ZeroPrepare] .done).seq secp256k1InPlaceDivisionSource).seq
    (.unitary [.ordinary fig15ZeroRestore] .done)
/-- The reversible zero-input extension adds no selected source corrections. -/
theorem secp256k1ZeroAllowedDivisionSource_certificate :
    secp256k1ZeroAllowedDivisionSource.erase=secp256k1ZeroAllowedDivision ∧
      secp256k1ZeroAllowedDivisionSource.events=12129750 := by
  constructor
  · simp [secp256k1ZeroAllowedDivisionSource,secp256k1ZeroAllowedDivision,CorrectionProgram.erase_seq,
      secp256k1InPlaceDivisionSource_certificate.1,CorrectionProgram.erase,correctionBlockErase,CorrectionFragment.erase]
  · simp [secp256k1ZeroAllowedDivisionSource,CorrectionProgram.events_seq,
      secp256k1InPlaceDivisionSource_certificate.2,CorrectionProgram.events,correctionBlockEvents,CorrectionFragment.events]
def secp256k1ZeroAllowedMultiplicationSource : CorrectionProgram :=
  ((CorrectionProgram.unitary [.ordinary fig15ZeroPrepare] .done).seq secp256k1InPlaceMultiplicationSource).seq
    (.unitary [.ordinary fig15ZeroRestore] .done)
/-- The reversible zero-input extension adds no selected source corrections. -/
theorem secp256k1ZeroAllowedMultiplicationSource_certificate :
    secp256k1ZeroAllowedMultiplicationSource.erase=secp256k1ZeroAllowedMultiplication ∧
      secp256k1ZeroAllowedMultiplicationSource.events=12129750 := by
  constructor
  · simp [secp256k1ZeroAllowedMultiplicationSource,secp256k1ZeroAllowedMultiplication,CorrectionProgram.erase_seq,
      secp256k1InPlaceMultiplicationSource_certificate.1,CorrectionProgram.erase,correctionBlockErase,CorrectionFragment.erase]
  · simp [secp256k1ZeroAllowedMultiplicationSource,CorrectionProgram.events_seq,
      secp256k1InPlaceMultiplicationSource_certificate.2,CorrectionProgram.events,correctionBlockEvents,CorrectionFragment.events]
end ShorECDLP.Paper2607_13816
