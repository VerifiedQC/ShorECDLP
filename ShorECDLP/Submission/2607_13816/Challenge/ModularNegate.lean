import ShorECDLP.Submission.«2607_13816».Challenge.ModularAdd
import ShorECDLP.Submission.«2607_13816».Window.NegativeControl

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

def prependCompiled {n start : Nat} (gs : Circuit)
    (p : (count : Nat) × Straight n start (start+count)) :
    (count : Nat) × Straight n start (start+count) := ⟨p.1, (literalProgram gs).append p.2⟩

theorem prependCompiled_run_eq {n start : Nat} (gs : Circuit)
    (p : (count : Nat) × Straight n start (start+count))
    (read : ConstantBit n → Bool) (history : Fin start → Bool) (target : AdaptiveCircuit)
    (hp : compiledRun p read history = target.run) :
    compiledRun (prependCompiled gs p) read history = (AdaptiveCircuit.unitary gs target).run := by
  simp only [prependCompiled, compiledRun, literalProgram_append_run, AdaptiveCircuit.run]
  exact congrArg _ hp

theorem appendCompiled_run_eq {n start : Nat} (p : (count : Nat) × Straight n start (start+count))
    (q : (count : Nat) × Straight n (start+p.1) (start+p.1+count))
    (read : ConstantBit n → Bool) (history : Fin start → Bool) (before after : AdaptiveCircuit)
    (hp : compiledRun p read history = before.run)
    (hq : ∀ h, compiledRun q read h = after.run) :
    compiledRun (appendCompiled p q) read history = (before.seq after).run := by
  rw [appendCompiled_run p q read history after hq, AdaptiveCircuit.run_seq]
  change (compiledRun p read history).seq after.run = _
  rw [hp, ← AdaptiveCircuit.run_seq]

def modularNegateProgram (n start : Nat) (target dirty : List Wire) (modulus : List Bool)
    (q c r t f : Wire) : (count : Nat) × Straight n start (start+count) :=
  let test := compareGEProgram n start target dirty 1 q c r t f
  let inc := gidneyProgram n (start+test.1) target (dirty.take (target.length-1))
    ((List.range target.length).map (Nat.testBit 1)) q c r t
  let add := gidneyProgram n (start+test.1+inc.1) target (dirty.take (target.length-1)) modulus f c r t
  let clear := compareGEProgram n (start+test.1+inc.1+add.1) target dirty 1 q c r t f
  appendCompiled test (prependCompiled (controlledComplement target q)
    (appendCompiled inc (appendCompiled add clear)))

attribute [local irreducible] compareGEProgram gidneyProgram

theorem modularNegateProgram_run (n start : Nat) (target dirty : List Wire) (modulus : List Bool)
    (q c r t f : Wire) (hd : target.length = dirty.length) (hk : modulus.length = target.length)
    (hpos : 0 < target.length) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (modularNegateProgram n start target dirty modulus q c r t f) read history =
      (controlledModularNegate target dirty modulus q c r t f).run := by
  have htake : target.length = (dirty.take (target.length-1)).length+1 := by
    rw [List.length_take, ← hd, Nat.min_eq_left (by omega)]
    omega
  unfold modularNegateProgram
  dsimp only
  unfold controlledModularNegate
  apply appendCompiled_run_eq
  · exact compareGEProgram_run n start target dirty 1 q c r t f hd read history
  · intro h
    apply prependCompiled_run_eq
    apply appendCompiled_run_eq
    · exact gidneyProgram_run n _ target _ _ q c r t htake (by simp) read h
    · intro h
      apply appendCompiled_run_eq
      · exact gidneyProgram_run n _ target _ modulus f c r t htake hk read h
      · intro h
        exact compareGEProgram_run n _ target dirty 1 q c r t f hd read h

theorem prependCompiled_tCount_eq {n start : Nat} (gs : Circuit)
    (p : (count : Nat) × Straight n start (start+count))
    (read : ConstantBit n → Bool) (history : Fin start → Bool) (target : AdaptiveCircuit)
    (hp : compiledTCount p read history = target.tCount) :
    compiledTCount (prependCompiled gs p) read history = (AdaptiveCircuit.unitary gs target).tCount := by
  simp only [prependCompiled, compiledTCount, literalProgram_append_tCount, AdaptiveCircuit.tCount]
  exact congrArg (ShorECDLP.tCount gs + ·) hp

theorem appendCompiled_tCount_eq {n start : Nat} (p : (count : Nat) × Straight n start (start+count))
    (q : (count : Nat) × Straight n (start+p.1) (start+p.1+count))
    (read : ConstantBit n → Bool) (history : Fin start → Bool) (before after : AdaptiveCircuit)
    (hp : compiledTCount p read history = before.tCount)
    (hq : ∀ h, compiledTCount q read h = after.tCount) :
    compiledTCount (appendCompiled p q) read history = (before.seq after).tCount := by
  rw [appendCompiled_tCount p q read history after.tCount hq, adaptive_tCount_seq]
  exact congrArg (· + after.tCount) hp

theorem modularNegateProgram_tCount (n start : Nat) (target dirty : List Wire) (modulus : List Bool)
    (q c r t f : Wire) (hd : target.length = dirty.length) (hk : modulus.length = target.length)
    (hpos : 0 < target.length) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (modularNegateProgram n start target dirty modulus q c r t f) read history =
      (controlledModularNegate target dirty modulus q c r t f).tCount := by
  have htake : target.length = (dirty.take (target.length-1)).length+1 := by
    rw [List.length_take, ← hd, Nat.min_eq_left (by omega)]
    omega
  unfold modularNegateProgram
  dsimp only
  unfold controlledModularNegate
  apply appendCompiled_tCount_eq
  · exact compareGEProgram_tCount n start target dirty 1 q c r t f hd read history
  · intro h
    apply prependCompiled_tCount_eq
    apply appendCompiled_tCount_eq
    · exact gidneyProgram_tCount n _ target _ _ q c r t htake (by simp) read h
    · intro h
      apply appendCompiled_tCount_eq
      · exact gidneyProgram_tCount n _ target _ modulus f c r t htake hk read h
      · intro h
        exact compareGEProgram_tCount n _ target dirty 1 q c r t f hd read h

def negativeNegateProgram (n start : Nat) (target dirty : List Wire) (modulus : List Bool)
    (q c r t f : Wire) : (count : Nat) × Straight n start (start+count) :=
  let p := modularNegateProgram n start target dirty modulus q c r t f
  prependCompiled [.X q] (appendCompiled p ⟨0, literalProgram [.X q]⟩)

theorem negativeNegateProgram_run (n start : Nat) (target dirty : List Wire) (modulus : List Bool)
    (q c r t f : Wire) (hd : target.length = dirty.length) (hk : modulus.length = target.length)
    (hpos : 0 < target.length) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (negativeNegateProgram n start target dirty modulus q c r t f) read history =
      (negativeControlledModularNegate target dirty modulus q c r t f).run := by
  unfold negativeNegateProgram negativeControlledModularNegate
  rw [adaptive_seq_assoc]
  change compiledRun (prependCompiled _ _) read history = (AdaptiveCircuit.unitary [.X q] _).run
  apply prependCompiled_run_eq
  apply appendCompiled_run_eq _ _ read history (controlledModularNegate target dirty modulus q c r t f)
    (.unitary [.X q] .done)
  · exact modularNegateProgram_run n start target dirty modulus q c r t f hd hk hpos read history
  · intro h
    exact literalProgram_run _ read h

theorem negativeNegateProgram_tCount (n start : Nat) (target dirty : List Wire) (modulus : List Bool)
    (q c r t f : Wire) (hd : target.length = dirty.length) (hk : modulus.length = target.length)
    (hpos : 0 < target.length) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (negativeNegateProgram n start target dirty modulus q c r t f) read history =
      (negativeControlledModularNegate target dirty modulus q c r t f).tCount := by
  unfold negativeNegateProgram negativeControlledModularNegate
  rw [adaptive_seq_assoc]
  change compiledTCount (prependCompiled _ _) read history = (AdaptiveCircuit.unitary [.X q] _).tCount
  apply prependCompiled_tCount_eq
  apply appendCompiled_tCount_eq _ _ read history (controlledModularNegate target dirty modulus q c r t f)
    (.unitary [.X q] .done)
  · exact modularNegateProgram_tCount n start target dirty modulus q c r t f hd hk hpos read history
  · intro h
    rfl

end ShorECDLP.Paper2607_13816.ChallengeMigration
