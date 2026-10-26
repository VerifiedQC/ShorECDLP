import ShorECDLP.Submission.«2607_13816».EEA.CoefficientPrefixInverse
import ShorECDLP.Submission.«2607_13816».Challenge.Unary
import ShorECDLP.Submission.«2607_13816».Challenge.VChain
import ShorECDLP.Submission.«2607_13816».EEA.CoefficientPrefix
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge
def coefficientFirstProgram (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (label : Nat) (control : Wire) :
    (count : Nat) × Straight n start (start+count) :=
  let body := rippleFirstProgram n start mode (r.accumulator k K) (r.targetAt target k label)
    (r.addendAt target k label) (r.carry k K) (r.cellScratch k K)
  appendCompiled body ⟨0, literalProgram [.CX control (r.accumulator k K)]⟩
theorem coefficientFirstProgram_run (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (label : Nat) (control : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (coefficientFirstProgram n start r k K mode target label control) read history =
      (coefficientPrefixFirstLeafAdaptive r k K mode target label control).run := by
  unfold coefficientFirstProgram coefficientPrefixFirstLeafAdaptive
  dsimp only
  apply appendCompiled_run_eq
  · exact rippleFirstProgram_run n start mode _ _ _ _ _ read history
  · intro h
    exact literalProgram_run _ read h

theorem coefficientFirstProgram_tCount (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (label : Nat) (control : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (coefficientFirstProgram n start r k K mode target label control) read history =
      (coefficientPrefixFirstLeafAdaptive r k K mode target label control).tCount := by
  unfold coefficientFirstProgram coefficientPrefixFirstLeafAdaptive
  dsimp only
  apply appendCompiled_tCount_eq
  · exact rippleFirstProgram_tCount n start mode _ _ _ _ _ read history
  · intro h
    simp [compiledTCount, literalProgram_tCount, AdaptiveCircuit.tCount]

def coefficientSecondProgram (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (label : Nat) (control : Wire) :
    (count : Nat) × Straight n start (start+count) :=
  let body := rippleSecondProgram n start mode (r.accumulator k K) (r.targetAt target k label)
    (r.addendAt target k label) (r.carry k K) (r.cellScratch k K)
  prependCompiled [.CX control (r.accumulator k K)] body
theorem coefficientSecondProgram_run (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (label : Nat) (control : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (coefficientSecondProgram n start r k K mode target label control) read history =
      (coefficientPrefixSecondLeafAdaptive r k K mode target label control).run := by
  unfold coefficientSecondProgram coefficientPrefixSecondLeafAdaptive
  dsimp only
  apply prependCompiled_run_eq
  exact rippleSecondProgram_run n start mode _ _ _ _ _ read history

theorem coefficientSecondProgram_tCount (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (target : CoefficientTarget) (label : Nat) (control : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (coefficientSecondProgram n start r k K mode target label control) read history =
      (coefficientPrefixSecondLeafAdaptive r k K mode target label control).tCount := by
  unfold coefficientSecondProgram coefficientPrefixSecondLeafAdaptive
  dsimp only
  apply prependCompiled_tCount_eq
  exact rippleSecondProgram_tCount n start mode _ _ _ _ _ read history

def coefficientProgram (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget) :
    (count : Nat) × Straight n start (start+count) :=
  let first := unaryProgram n .inc (fun label control cursor =>
    coefficientFirstProgram n cursor r k K mode target label control)
    (coefficientPrefixTree r k K) r.control (r.path k K) start
  let second := unaryProgram n .dec (fun label control cursor =>
    coefficientSecondProgram n cursor r k K mode target label control)
    (coefficientPrefixTree r k K) r.control (r.path k K) (start+first.1)
  prependCompiled [.CX r.control (r.accumulator k K)]
    (appendCompiled first (prependCompiled (coefficientPrefixSignCircuit r k K signUpdate)
      (appendCompiled second ⟨0, literalProgram [.CX r.control (r.accumulator k K)]⟩)))
theorem coefficientProgram_run (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (coefficientProgram n start r k K mode signUpdate target) read history =
      (coefficientPrefixAdaptive r k K mode signUpdate target).run := by
  unfold coefficientProgram coefficientPrefixAdaptive
  dsimp only
  apply prependCompiled_run_eq
  apply appendCompiled_run_eq
  · apply unaryProgram_run
    intro label control cursor h
    exact coefficientFirstProgram_run n cursor r k K mode target label control read h
  · intro h
    apply prependCompiled_run_eq
    apply appendCompiled_run_eq
    · apply unaryProgram_run
      intro label control cursor h
      exact coefficientSecondProgram_run n cursor r k K mode target label control read h
    · intro h
      exact literalProgram_run _ read h

theorem coefficientProgram_tCount (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (coefficientProgram n start r k K mode signUpdate target) read history =
      (coefficientPrefixAdaptive r k K mode signUpdate target).tCount := by
  unfold coefficientProgram coefficientPrefixAdaptive
  dsimp only
  apply prependCompiled_tCount_eq
  apply appendCompiled_tCount_eq
  · apply unaryProgram_tCount
    intro label control cursor h
    exact coefficientFirstProgram_tCount n cursor r k K mode target label control read h
  · intro h
    apply prependCompiled_tCount_eq
    apply appendCompiled_tCount_eq
    · apply unaryProgram_tCount
      intro label control cursor h
      exact coefficientSecondProgram_tCount n cursor r k K mode target label control read h
    · intro h
      simp [compiledTCount, literalProgram_tCount, AdaptiveCircuit.tCount]

def coefficientInverseProgram (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget) :
    (count : Nat) × Straight n start (start+count) :=
  coefficientProgram n start r k K mode.inverse signUpdate target
theorem coefficientInverseProgram_run (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (coefficientInverseProgram n start r k K mode signUpdate target) read history =
      (coefficientPrefixInverseAdaptive r k K mode signUpdate target).run :=
  coefficientProgram_run n start r k K mode.inverse signUpdate target read history

theorem coefficientInverseProgram_tCount (n start : Nat) (r : CoefficientPrefixRegisters) (k K : Nat)
    (mode : RippleMode) (signUpdate : Bool) (target : CoefficientTarget)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (coefficientInverseProgram n start r k K mode signUpdate target) read history =
      (coefficientPrefixInverseAdaptive r k K mode signUpdate target).tCount :=
  coefficientProgram_tCount n start r k K mode.inverse signUpdate target read history

end ShorECDLP.Paper2607_13816.ChallengeMigration
