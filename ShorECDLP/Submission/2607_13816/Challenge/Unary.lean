import ShorECDLP.Submission.«2607_13816».Challenge.ModularNegate
import ShorECDLP.Submission.«2607_13816».EEA.UnaryAction
/-! Compile the fixed unary decoder tree in either traversal order. The leaf
compiler depends only on static labels, wire addresses and cursor lengths, never
on a public point or measurement history. The resulting Straight contains no callbacks. -/
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

def zeroEraseProgram (n start : Nat) (a b w : Wire) : (count : Nat) × Straight n start (start+count) :=
  prependCompiled [.X b] (appendCompiled ⟨1, andEraseProgram n start a b w⟩
    ⟨0, literalProgram [.X b]⟩)

theorem zeroEraseProgram_run (n start : Nat) (a b w : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (zeroEraseProgram n start a b w) read history = (eraseZeroAnd a b w).run := by
  unfold zeroEraseProgram eraseZeroAnd
  change _ = (AdaptiveCircuit.unitary [.X b] ((measuredAndErase a b w).seq (.unitary [.X b] .done))).run
  apply prependCompiled_run_eq
  apply appendCompiled_run_eq
  · exact andEraseProgram_run n start a b w read history
  · intro h
    exact literalProgram_run _ read h

def unaryProgram (n : Nat) (order : UnaryOrder)
    (leaf : (label : Nat) → (control : Wire) → (start : Nat) →
      (count : Nat) × Straight n start (start+count)) :
    UnaryActionTree → Wire → List Wire → (start : Nat) → (count : Nat) × Straight n start (start+count)
  | .leaf label, control, _, start => leaf label control start
  | .node bit zero one, control, path::rest, start =>
    let first := unaryProgram n order leaf (if order = .inc then zero else one) path rest start
    let second := unaryProgram n order leaf (if order = .inc then one else zero) path rest (start+first.1)
    let clear := zeroEraseProgram n (start+first.1+second.1) control bit path
    if order = .inc then
      prependCompiled (computeZeroAnd control bit path)
        (appendCompiled first (prependCompiled [.CX control path]
          (appendCompiled second (prependCompiled [.CX control path] clear))))
    else
      prependCompiled (computeZeroAnd control bit path)
        (prependCompiled [.CX control path] (appendCompiled first
          (prependCompiled [.CX control path] (appendCompiled second clear))))
  | .node _ _ _, _, [], _ => ⟨0, .done⟩
termination_by tree => tree
decreasing_by all_goals (split <;> simp_all); all_goals omega


theorem unaryProgram_run (n : Nat) (order : UnaryOrder)
    (leaf : (label : Nat) → (control : Wire) → (start : Nat) →
      (count : Nat) × Straight n start (start+count))
    (source : Nat → Wire → AdaptiveCircuit) (read : ConstantBit n → Bool)
    (hleaf : ∀ label control start h, compiledRun (leaf label control start) read h = (source label control).run)
    (tree : UnaryActionTree) (control : Wire) (paths : List Wire) (start : Nat)
    (history : Fin start → Bool) :
    compiledRun (unaryProgram n order leaf tree control paths start) read history =
      (unaryAdaptiveAction order source tree control paths).run := by
  induction tree generalizing control paths start with
  | leaf label => simpa only [unaryProgram, unaryAdaptiveAction] using hleaf label control start history
  | node bit zero one ihz iho =>
    cases paths with
    | nil => simp only [unaryProgram, unaryAdaptiveAction]; rfl
    | cons path rest =>
      cases order with
      | inc =>
        simp only [unaryProgram, unaryAdaptiveAction]
        apply prependCompiled_run_eq
        apply appendCompiled_run_eq
        · exact ihz path rest start history
        · intro h
          apply prependCompiled_run_eq
          apply appendCompiled_run_eq
          · exact iho path rest _ h
          · intro h
            apply prependCompiled_run_eq
            exact zeroEraseProgram_run n _ control bit path read h
      | dec =>
        simp only [unaryProgram, unaryAdaptiveAction]
        apply prependCompiled_run_eq
        apply prependCompiled_run_eq
        apply appendCompiled_run_eq
        · exact iho path rest start history
        · intro h
          apply prependCompiled_run_eq
          apply appendCompiled_run_eq
          · exact ihz path rest _ h
          · intro h
            exact zeroEraseProgram_run n _ control bit path read h

theorem zeroEraseProgram_tCount (n start : Nat) (a b w : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (zeroEraseProgram n start a b w) read history = (eraseZeroAnd a b w).tCount := by
  unfold zeroEraseProgram eraseZeroAnd
  change _ = (AdaptiveCircuit.unitary [.X b] ((measuredAndErase a b w).seq (.unitary [.X b] .done))).tCount
  apply prependCompiled_tCount_eq
  apply appendCompiled_tCount_eq
  · change ((andEraseProgram n start a b w).instantiate read history).tCount = _
    rw [andEraseProgram_tCount]
    simp [measuredAndErase, measureResetWithCorrection, measuredAndCorrection,
      AdaptiveCircuit.tCount, controlledZ, ShorECDLP.tCount, tCost]
  · intro h
    rfl

theorem unaryProgram_tCount (n : Nat) (order : UnaryOrder)
    (leaf : (label : Nat) → (control : Wire) → (start : Nat) →
      (count : Nat) × Straight n start (start+count))
    (source : Nat → Wire → AdaptiveCircuit) (read : ConstantBit n → Bool)
    (hleaf : ∀ label control start h, compiledTCount (leaf label control start) read h = (source label control).tCount)
    (tree : UnaryActionTree) (control : Wire) (paths : List Wire) (start : Nat)
    (history : Fin start → Bool) :
    compiledTCount (unaryProgram n order leaf tree control paths start) read history =
      (unaryAdaptiveAction order source tree control paths).tCount := by
  induction tree generalizing control paths start with
  | leaf label => simpa only [unaryProgram, unaryAdaptiveAction] using hleaf label control start history
  | node bit zero one ihz iho =>
    cases paths with
    | nil => simp only [unaryProgram, unaryAdaptiveAction]; rfl
    | cons path rest =>
      cases order with
      | inc =>
        simp only [unaryProgram, unaryAdaptiveAction]
        apply prependCompiled_tCount_eq
        apply appendCompiled_tCount_eq
        · exact ihz path rest start history
        · intro h
          apply prependCompiled_tCount_eq
          apply appendCompiled_tCount_eq
          · exact iho path rest _ h
          · intro h
            apply prependCompiled_tCount_eq
            exact zeroEraseProgram_tCount n _ control bit path read h
      | dec =>
        simp only [unaryProgram, unaryAdaptiveAction]
        apply prependCompiled_tCount_eq
        apply prependCompiled_tCount_eq
        apply appendCompiled_tCount_eq
        · exact iho path rest start history
        · intro h
          apply prependCompiled_tCount_eq
          apply appendCompiled_tCount_eq
          · exact ihz path rest _ h
          · intro h
            exact zeroEraseProgram_tCount n _ control bit path read h

end ShorECDLP.Paper2607_13816.ChallengeMigration
