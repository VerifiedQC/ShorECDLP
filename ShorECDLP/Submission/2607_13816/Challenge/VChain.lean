import ShorECDLP.Submission.«2607_13816».Challenge.ModularNegate
import ShorECDLP.Submission.«2607_13816».EEA.IntervalLeaf
/-! Source-order measured v-chain and ripple cells. The total definitions also
preserve source fallbacks for insufficient scratch; physical correctness and
source-capacity preconditions remain the responsibility of the existing layout proofs. -/
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

def vchainTailProgram (n : Nat) : (controls : List Wire) → (acc target : Wire) →
    (scratch : List Wire) → (start : Nat) → (count : Nat) × Straight n start (start+count)
  | [], _, _, _, _ => ⟨0, .done⟩
  | [control], acc, target, _, _ => ⟨0, literalProgram [.CCX control acc target]⟩
  | control::next::controls, acc, target, work::scratch, start =>
    let body := vchainTailProgram n (next::controls) work target scratch start
    prependCompiled [.CCX control acc work]
      (appendCompiled body ⟨1, andEraseProgram n (start+body.1) control acc work⟩)
  | _::_::_, _, _, [], _ => ⟨0, .done⟩

theorem vchainTailProgram_run (n : Nat) (controls : List Wire) (acc target : Wire)
    (scratch : List Wire) (start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (vchainTailProgram n controls acc target scratch start) read history =
      (mcxVChainTailAdaptive acc controls target scratch).run := by
  induction controls generalizing acc scratch start with
  | nil => rfl
  | cons control controls ih =>
    cases controls with
    | nil =>
      exact literalProgram_run _ read history
    | cons next controls =>
      cases scratch with
      | nil => rfl
      | cons work scratch =>
        simp only [vchainTailProgram, mcxVChainTailAdaptive]
        apply prependCompiled_run_eq
        apply appendCompiled_run_eq
        · exact ih work scratch start history
        · intro h
          exact andEraseProgram_run n _ control acc work read h

theorem vchainTailProgram_tCount (n : Nat) (controls : List Wire) (acc target : Wire)
    (scratch : List Wire) (start : Nat) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (vchainTailProgram n controls acc target scratch start) read history =
      (mcxVChainTailAdaptive acc controls target scratch).tCount := by
  induction controls generalizing acc scratch start with
  | nil => rfl
  | cons control controls ih =>
    cases controls with
    | nil =>
      simp [vchainTailProgram, compiledTCount, mcxVChainTailAdaptive, literalProgram_tCount, AdaptiveCircuit.tCount]
    | cons next controls =>
      cases scratch with
      | nil => rfl
      | cons work scratch =>
        simp only [vchainTailProgram, mcxVChainTailAdaptive]
        apply prependCompiled_tCount_eq
        apply appendCompiled_tCount_eq
        · exact ih work scratch start history
        · intro h
          change ((andEraseProgram n _ control acc work).instantiate read h).tCount = _
          rw [andEraseProgram_tCount]
          simp [measuredAndErase, measureResetWithCorrection, measuredAndCorrection,
            AdaptiveCircuit.tCount, controlledZ, ShorECDLP.tCount, tCost]

def vchainProgram (n start : Nat) (controls : List Wire) (target : Wire) (scratch : List Wire) :
    (count : Nat) × Straight n start (start+count) :=
  match controls with
  | [] => ⟨0, literalProgram [.X target]⟩
  | [control] => ⟨0, literalProgram [.CX control target]⟩
  | first::second::rest => vchainTailProgram n (first::rest) second target scratch start
theorem vchainProgram_run (n start : Nat) (controls : List Wire) (target : Wire)
    (scratch : List Wire) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (vchainProgram n start controls target scratch) read history =
      (mcxVChainAdaptive controls target scratch).run := by
  cases controls with
  | nil =>
    exact literalProgram_run _ read history
  | cons first rest =>
    cases rest with
    | nil =>
      exact literalProgram_run _ read history
    | cons second rest =>
      exact vchainTailProgram_run n (first::rest) second target scratch start read history

theorem vchainProgram_tCount (n start : Nat) (controls : List Wire) (target : Wire)
    (scratch : List Wire) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (vchainProgram n start controls target scratch) read history =
      (mcxVChainAdaptive controls target scratch).tCount := by
  cases controls with
  | nil =>
    simp [vchainProgram, compiledTCount, mcxVChainAdaptive, literalProgram_tCount, AdaptiveCircuit.tCount]
  | cons first rest =>
    cases rest with
    | nil =>
      simp [vchainProgram, compiledTCount, mcxVChainAdaptive, literalProgram_tCount, AdaptiveCircuit.tCount]
    | cons second rest =>
      exact vchainTailProgram_tCount n (first::rest) second target scratch start read history

def rippleMajProgram (n start : Nat) (control target addend carry scratch : Wire) :
    (count : Nat) × Straight n start (start+count) :=
  let body := vchainProgram n start ([control, target, addend] : List Wire) carry ([scratch] : List Wire)
  prependCompiled [.CX carry target, .CX carry addend] body
theorem rippleMajProgram_run (n start : Nat) (control target addend carry scratch : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (rippleMajProgram n start control target addend carry scratch) read history =
      (controlledMajAdaptive control target addend carry scratch).run := by
  unfold rippleMajProgram controlledMajAdaptive cleanC3XAdaptive
  dsimp only
  apply prependCompiled_run_eq
  exact vchainProgram_run n start _ carry ([scratch] : List Wire) read history

theorem rippleMajProgram_tCount (n start : Nat) (control target addend carry scratch : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (rippleMajProgram n start control target addend carry scratch) read history =
      (controlledMajAdaptive control target addend carry scratch).tCount := by
  unfold rippleMajProgram controlledMajAdaptive cleanC3XAdaptive
  dsimp only
  apply prependCompiled_tCount_eq
  exact vchainProgram_tCount n start _ carry ([scratch] : List Wire) read history

def rippleUmaProgram (n start : Nat) (control target addend carry scratch : Wire) :
    (count : Nat) × Straight n start (start+count) :=
  let body := vchainProgram n start ([control, target, addend] : List Wire) carry ([scratch] : List Wire)
  appendCompiled body ⟨0, literalProgram [.CCX control addend target, .CX carry addend, .CX carry target]⟩
theorem rippleUmaProgram_run (n start : Nat) (control target addend carry scratch : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (rippleUmaProgram n start control target addend carry scratch) read history =
      (controlledUmaAdaptive control target addend carry scratch).run := by
  unfold rippleUmaProgram controlledUmaAdaptive cleanC3XAdaptive
  dsimp only
  apply appendCompiled_run_eq
  · exact vchainProgram_run n start _ carry ([scratch] : List Wire) read history
  · intro h
    exact literalProgram_run _ read h

theorem rippleUmaProgram_tCount (n start : Nat) (control target addend carry scratch : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (rippleUmaProgram n start control target addend carry scratch) read history =
      (controlledUmaAdaptive control target addend carry scratch).tCount := by
  unfold rippleUmaProgram controlledUmaAdaptive cleanC3XAdaptive
  dsimp only
  apply appendCompiled_tCount_eq
  · exact vchainProgram_tCount n start _ carry ([scratch] : List Wire) read history
  · intro h
    simp [compiledTCount, literalProgram_tCount, AdaptiveCircuit.tCount]

def rippleMajInvProgram (n start : Nat) (control target addend carry scratch : Wire) :
    (count : Nat) × Straight n start (start+count) :=
  let body := vchainProgram n start ([control, target, addend] : List Wire) carry ([scratch] : List Wire)
  appendCompiled body ⟨0, literalProgram [.CX carry addend, .CX carry target]⟩
theorem rippleMajInvProgram_run (n start : Nat) (control target addend carry scratch : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (rippleMajInvProgram n start control target addend carry scratch) read history =
      (controlledMajInvAdaptive control target addend carry scratch).run := by
  unfold rippleMajInvProgram controlledMajInvAdaptive cleanC3XAdaptive
  dsimp only
  apply appendCompiled_run_eq
  · exact vchainProgram_run n start _ carry ([scratch] : List Wire) read history
  · intro h
    exact literalProgram_run _ read h

theorem rippleMajInvProgram_tCount (n start : Nat) (control target addend carry scratch : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (rippleMajInvProgram n start control target addend carry scratch) read history =
      (controlledMajInvAdaptive control target addend carry scratch).tCount := by
  unfold rippleMajInvProgram controlledMajInvAdaptive cleanC3XAdaptive
  dsimp only
  apply appendCompiled_tCount_eq
  · exact vchainProgram_tCount n start _ carry ([scratch] : List Wire) read history
  · intro h
    simp [compiledTCount, literalProgram_tCount, AdaptiveCircuit.tCount]

def rippleUmaInvProgram (n start : Nat) (control target addend carry scratch : Wire) :
    (count : Nat) × Straight n start (start+count) :=
  let body := vchainProgram n start ([control, target, addend] : List Wire) carry ([scratch] : List Wire)
  prependCompiled [.CX carry target, .CX carry addend, .CCX control addend target] body
theorem rippleUmaInvProgram_run (n start : Nat) (control target addend carry scratch : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (rippleUmaInvProgram n start control target addend carry scratch) read history =
      (controlledUmaInvAdaptive control target addend carry scratch).run := by
  unfold rippleUmaInvProgram controlledUmaInvAdaptive cleanC3XAdaptive
  dsimp only
  apply prependCompiled_run_eq
  exact vchainProgram_run n start _ carry ([scratch] : List Wire) read history

theorem rippleUmaInvProgram_tCount (n start : Nat) (control target addend carry scratch : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (rippleUmaInvProgram n start control target addend carry scratch) read history =
      (controlledUmaInvAdaptive control target addend carry scratch).tCount := by
  unfold rippleUmaInvProgram controlledUmaInvAdaptive cleanC3XAdaptive
  dsimp only
  apply prependCompiled_tCount_eq
  exact vchainProgram_tCount n start _ carry ([scratch] : List Wire) read history

def rippleFirstProgram (n start : Nat) (mode : RippleMode) (control target addend carry scratch : Wire) :
    (count : Nat) × Straight n start (start+count) :=
  match mode with
  | .add => rippleMajProgram n start control target addend carry scratch
  | .sub => rippleUmaInvProgram n start control target addend carry scratch
theorem rippleFirstProgram_run (n start : Nat) (mode : RippleMode) (control target addend carry scratch : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (rippleFirstProgram n start mode control target addend carry scratch) read history =
      (rippleFirstCellAdaptive mode control target addend carry scratch).run := by
  cases mode with
  | add => exact rippleMajProgram_run n start control target addend carry scratch read history
  | sub => exact rippleUmaInvProgram_run n start control target addend carry scratch read history

theorem rippleFirstProgram_tCount (n start : Nat) (mode : RippleMode) (control target addend carry scratch : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (rippleFirstProgram n start mode control target addend carry scratch) read history =
      (rippleFirstCellAdaptive mode control target addend carry scratch).tCount := by
  cases mode with
  | add => exact rippleMajProgram_tCount n start control target addend carry scratch read history
  | sub => exact rippleUmaInvProgram_tCount n start control target addend carry scratch read history

def rippleSecondProgram (n start : Nat) (mode : RippleMode) (control target addend carry scratch : Wire) :
    (count : Nat) × Straight n start (start+count) :=
  match mode with
  | .add => rippleUmaProgram n start control target addend carry scratch
  | .sub => rippleMajInvProgram n start control target addend carry scratch
theorem rippleSecondProgram_run (n start : Nat) (mode : RippleMode) (control target addend carry scratch : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (rippleSecondProgram n start mode control target addend carry scratch) read history =
      (rippleSecondCellAdaptive mode control target addend carry scratch).run := by
  cases mode with
  | add => exact rippleUmaProgram_run n start control target addend carry scratch read history
  | sub => exact rippleMajInvProgram_run n start control target addend carry scratch read history

theorem rippleSecondProgram_tCount (n start : Nat) (mode : RippleMode) (control target addend carry scratch : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (rippleSecondProgram n start mode control target addend carry scratch) read history =
      (rippleSecondCellAdaptive mode control target addend carry scratch).tCount := by
  cases mode with
  | add => exact rippleUmaProgram_tCount n start control target addend carry scratch read history
  | sub => exact rippleMajInvProgram_tCount n start control target addend carry scratch read history

end ShorECDLP.Paper2607_13816.ChallengeMigration
