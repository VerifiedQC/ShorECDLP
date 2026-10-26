import ShorECDLP.Submission.«2607_13816».Challenge.Unary
import ShorECDLP.Submission.«2607_13816».EEA.DualUnaryAction
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

def dualEraseProgram (n start : Nat) (a i x b j y : Wire) :
    (count : Nat) × Straight n start (start+count) :=
  let first := zeroEraseProgram n start b j y
  appendCompiled first (zeroEraseProgram n (start+first.1) a i x)
theorem dualEraseProgram_run (n start : Nat) (a i x b j y : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (dualEraseProgram n start a i x b j y) read history = (eraseDualZeroAnd a i x b j y).run := by
  unfold dualEraseProgram eraseDualZeroAnd
  dsimp only
  apply appendCompiled_run_eq
  · exact zeroEraseProgram_run n start b j y read history
  · intro h
    exact zeroEraseProgram_run n _ a i x read h

theorem dualEraseProgram_tCount (n start : Nat) (a i x b j y : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (dualEraseProgram n start a i x b j y) read history = (eraseDualZeroAnd a i x b j y).tCount := by
  unfold dualEraseProgram eraseDualZeroAnd
  dsimp only
  apply appendCompiled_tCount_eq
  · exact zeroEraseProgram_tCount n start b j y read history
  · intro h
    exact zeroEraseProgram_tCount n _ a i x read h

def dualProgram (n : Nat) (order : UnaryOrder)
    (leaf : (label : Nat) → (a b : Wire) → (start : Nat) →
      (count : Nat) × Straight n start (start+count)) :
    DualUnaryActionTree → Wire → Wire → List Wire → List Wire → (start : Nat) →
      (count : Nat) × Straight n start (start+count)
  | .leaf label, a, b, _, _, start => leaf label a b start
  | .node i j zero one, a, b, x::xs, y::ys, start =>
    let first := dualProgram n order leaf (if order = .inc then zero else one) x y xs ys start
    let second := dualProgram n order leaf (if order = .inc then one else zero) x y xs ys (start+first.1)
    let clear := dualEraseProgram n (start+first.1+second.1) a i x b j y
    if order = .inc then
      prependCompiled (computeZeroAnd a i x) (prependCompiled (computeZeroAnd b j y)
        (appendCompiled first (prependCompiled [.CX a x, .CX b y]
          (appendCompiled second (prependCompiled [.CX b y, .CX a x] clear)))))
    else
      prependCompiled (computeZeroAnd a i x) (prependCompiled (computeZeroAnd b j y)
        (prependCompiled [.CX a x, .CX b y] (appendCompiled first
          (prependCompiled [.CX b y, .CX a x] (appendCompiled second clear)))))
  | .node _ _ _ _, _, _, _, _, _ => ⟨0, .done⟩
termination_by tree => tree
decreasing_by all_goals (split <;> simp_all); all_goals omega

theorem dualProgram_run (n : Nat) (order : UnaryOrder)
    (leaf : (label : Nat) → (a b : Wire) → (start : Nat) →
      (count : Nat) × Straight n start (start+count))
    (source : Nat → Wire → Wire → AdaptiveCircuit) (read : ConstantBit n → Bool)
    (hleaf : ∀ label a b start h, compiledRun (leaf label a b start) read h = (source label a b).run)
    (tree : DualUnaryActionTree) (a b : Wire) (xs ys : List Wire) (start : Nat) (history : Fin start → Bool) :
    compiledRun (dualProgram n order leaf tree a b xs ys start) read history =
      (dualUnaryAdaptiveAction order source tree a b xs ys).run := by
  induction tree generalizing a b xs ys start with
  | leaf label => simpa only [dualProgram, dualUnaryAdaptiveAction] using hleaf label a b start history
  | node i j zero one ihz iho =>
    cases xs with
    | nil => simp only [dualProgram, dualUnaryAdaptiveAction]; rfl
    | cons x xs =>
      cases ys with
      | nil => simp only [dualProgram, dualUnaryAdaptiveAction]; rfl
      | cons y ys =>
        cases order with
        | inc =>
          simp only [dualProgram, dualUnaryAdaptiveAction]
          apply prependCompiled_run_eq
          apply prependCompiled_run_eq
          apply appendCompiled_run_eq
          · exact ihz x y xs ys start history
          · intro h
            apply prependCompiled_run_eq
            apply appendCompiled_run_eq
            · exact iho x y xs ys _ h
            · intro h
              apply prependCompiled_run_eq
              exact dualEraseProgram_run n _ a i x b j y read h
        | dec =>
          simp only [dualProgram, dualUnaryAdaptiveAction]
          apply prependCompiled_run_eq
          apply prependCompiled_run_eq
          apply prependCompiled_run_eq
          apply appendCompiled_run_eq
          · exact iho x y xs ys start history
          · intro h
            apply prependCompiled_run_eq
            apply appendCompiled_run_eq
            · exact ihz x y xs ys _ h
            · intro h
              exact dualEraseProgram_run n _ a i x b j y read h

theorem dualProgram_tCount (n : Nat) (order : UnaryOrder)
    (leaf : (label : Nat) → (a b : Wire) → (start : Nat) →
      (count : Nat) × Straight n start (start+count))
    (source : Nat → Wire → Wire → AdaptiveCircuit) (read : ConstantBit n → Bool)
    (hleaf : ∀ label a b start h, compiledTCount (leaf label a b start) read h = (source label a b).tCount)
    (tree : DualUnaryActionTree) (a b : Wire) (xs ys : List Wire) (start : Nat) (history : Fin start → Bool) :
    compiledTCount (dualProgram n order leaf tree a b xs ys start) read history =
      (dualUnaryAdaptiveAction order source tree a b xs ys).tCount := by
  induction tree generalizing a b xs ys start with
  | leaf label => simpa only [dualProgram, dualUnaryAdaptiveAction] using hleaf label a b start history
  | node i j zero one ihz iho =>
    cases xs with
    | nil => simp only [dualProgram, dualUnaryAdaptiveAction]; rfl
    | cons x xs =>
      cases ys with
      | nil => simp only [dualProgram, dualUnaryAdaptiveAction]; rfl
      | cons y ys =>
        cases order with
        | inc =>
          simp only [dualProgram, dualUnaryAdaptiveAction]
          apply prependCompiled_tCount_eq
          apply prependCompiled_tCount_eq
          apply appendCompiled_tCount_eq
          · exact ihz x y xs ys start history
          · intro h
            apply prependCompiled_tCount_eq
            apply appendCompiled_tCount_eq
            · exact iho x y xs ys _ h
            · intro h
              apply prependCompiled_tCount_eq
              exact dualEraseProgram_tCount n _ a i x b j y read h
        | dec =>
          simp only [dualProgram, dualUnaryAdaptiveAction]
          apply prependCompiled_tCount_eq
          apply prependCompiled_tCount_eq
          apply prependCompiled_tCount_eq
          apply appendCompiled_tCount_eq
          · exact iho x y xs ys start history
          · intro h
            apply prependCompiled_tCount_eq
            apply appendCompiled_tCount_eq
            · exact ihz x y xs ys _ h
            · intro h
              exact dualEraseProgram_tCount n _ a i x b j y read h

end ShorECDLP.Paper2607_13816.ChallengeMigration
