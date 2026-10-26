import ShorECDLP.Submission.«2607_13816».Challenge.ModularNegate
import ShorECDLP.Submission.«2607_13816».EEA.ParityCorrection
/-! Fixed preprocessing and parity schedules for the EEA wrapper. These
components preserve source execution; the full indexed EEA schedule is separate. -/
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

def constMinusProgram (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (q c r t : Wire) : (count : Nat) × Straight n start (start+count) :=
  let inc := gidneyProgram n start input dirty ((List.range input.length).map (Nat.testBit 1)) q c r t
  prependCompiled (controlledComplement input q)
    (appendCompiled inc (gidneyProgram n (start+inc.1) input dirty bits q c r t))
attribute [local irreducible] gidneyProgram uncontrolledCompareProgram
theorem constMinusProgram_run (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (q c r t : Wire) (hd : input.length = dirty.length+1) (hk : bits.length = input.length)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (constMinusProgram n start input dirty bits q c r t) read history =
      (controlledConstMinus input dirty bits q c r t).run := by
  unfold constMinusProgram controlledConstMinus
  dsimp only
  apply prependCompiled_run_eq
  apply appendCompiled_run_eq
  · exact gidneyProgram_run n _ input dirty _ q c r t hd (by simp) read history
  · intro h
    exact gidneyProgram_run n _ input dirty bits q c r t hd hk read h

theorem constMinusProgram_tCount (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (q c r t : Wire) (hd : input.length = dirty.length+1) (hk : bits.length = input.length)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (constMinusProgram n start input dirty bits q c r t) read history =
      (controlledConstMinus input dirty bits q c r t).tCount := by
  unfold constMinusProgram controlledConstMinus
  dsimp only
  apply prependCompiled_tCount_eq
  apply appendCompiled_tCount_eq
  · exact gidneyProgram_tCount n _ input dirty _ q c r t hd (by simp) read history
  · intro h
    exact gidneyProgram_tCount n _ input dirty bits q c r t hd hk read h

def eeaCenterProgram (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t iter : Wire) : (count : Nat) × Straight n start (start+count) :=
  let test := uncontrolledCompareProgram n start input dirty (p/2+1) c r t iter
  let neg := constMinusProgram n (start+test.1) input (dirty.take (input.length-1)) bits iter c r t
  appendCompiled test neg
theorem eeaCenterProgram_run (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t iter : Wire) (hd : input.length = dirty.length)
    (hk : bits.length = input.length) (hpos : 0 < input.length)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (eeaCenterProgram n start input dirty bits p c r t iter) read history =
      (eeaCenter input dirty bits p c r t iter).run := by
  have ht : input.length = (dirty.take (input.length-1)).length+1 := by
    rw [List.length_take, ← hd, Nat.min_eq_left (Nat.sub_le _ _)]
    omega
  unfold eeaCenterProgram eeaCenter
  dsimp only
  apply appendCompiled_run_eq
  · exact uncontrolledCompareProgram_run n _ input dirty (p/2+1) c r t iter hd read history
  · intro h
    exact constMinusProgram_run n _ input _ bits iter c r t ht hk read h

theorem eeaCenterProgram_tCount (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t iter : Wire) (hd : input.length = dirty.length)
    (hk : bits.length = input.length) (hpos : 0 < input.length)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (eeaCenterProgram n start input dirty bits p c r t iter) read history =
      (eeaCenter input dirty bits p c r t iter).tCount := by
  have ht : input.length = (dirty.take (input.length-1)).length+1 := by
    rw [List.length_take, ← hd, Nat.min_eq_left (Nat.sub_le _ _)]
    omega
  unfold eeaCenterProgram eeaCenter
  dsimp only
  apply appendCompiled_tCount_eq
  · exact uncontrolledCompareProgram_tCount n _ input dirty (p/2+1) c r t iter hd read history
  · intro h
    exact constMinusProgram_tCount n _ input _ bits iter c r t ht hk read h

def eeaUncenterProgram (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t iter : Wire) : (count : Nat) × Straight n start (start+count) :=
  let neg := constMinusProgram n start input (dirty.take (input.length-1)) bits iter c r t
  let test := uncontrolledCompareProgram n (start+neg.1) input dirty (p/2+1) c r t iter
  appendCompiled neg test
theorem eeaUncenterProgram_run (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t iter : Wire) (hd : input.length = dirty.length)
    (hk : bits.length = input.length) (hpos : 0 < input.length)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (eeaUncenterProgram n start input dirty bits p c r t iter) read history =
      (eeaUncenter input dirty bits p c r t iter).run := by
  have ht : input.length = (dirty.take (input.length-1)).length+1 := by
    rw [List.length_take, ← hd, Nat.min_eq_left (Nat.sub_le _ _)]
    omega
  unfold eeaUncenterProgram eeaUncenter
  dsimp only
  apply appendCompiled_run_eq
  · exact constMinusProgram_run n _ input _ bits iter c r t ht hk read history
  · intro h
    exact uncontrolledCompareProgram_run n _ input dirty (p/2+1) c r t iter hd read h

theorem eeaUncenterProgram_tCount (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t iter : Wire) (hd : input.length = dirty.length)
    (hk : bits.length = input.length) (hpos : 0 < input.length)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (eeaUncenterProgram n start input dirty bits p c r t iter) read history =
      (eeaUncenter input dirty bits p c r t iter).tCount := by
  have ht : input.length = (dirty.take (input.length-1)).length+1 := by
    rw [List.length_take, ← hd, Nat.min_eq_left (Nat.sub_le _ _)]
    omega
  unfold eeaUncenterProgram eeaUncenter
  dsimp only
  apply appendCompiled_tCount_eq
  · exact constMinusProgram_tCount n _ input _ bits iter c r t ht hk read history
  · intro h
    exact uncontrolledCompareProgram_tCount n _ input dirty (p/2+1) c r t iter hd read h

def eeaParityProgram (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (c r t iter : Wire) : (count : Nat) × Straight n start (start+count) :=
  let body := constMinusProgram n start input dirty bits iter c r t
  prependCompiled [.X iter] (appendCompiled body ⟨0, literalProgram [.X iter]⟩)
theorem eeaParityProgram_run (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (c r t iter : Wire) (hd : input.length = dirty.length+1) (hk : bits.length = input.length)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (eeaParityProgram n start input dirty bits c r t iter) read history =
      (eeaParityCorrection input dirty bits c r t iter).run := by
  unfold eeaParityProgram eeaParityCorrection
  dsimp only
  apply prependCompiled_run_eq
  apply appendCompiled_run_eq
  · exact constMinusProgram_run n _ input dirty bits iter c r t hd hk read history
  · intro h
    exact literalProgram_run _ read h

theorem eeaParityProgram_tCount (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (c r t iter : Wire) (hd : input.length = dirty.length+1) (hk : bits.length = input.length)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (eeaParityProgram n start input dirty bits c r t iter) read history =
      (eeaParityCorrection input dirty bits c r t iter).tCount := by
  unfold eeaParityProgram eeaParityCorrection
  dsimp only
  apply prependCompiled_tCount_eq
  apply appendCompiled_tCount_eq
  · exact constMinusProgram_tCount n _ input dirty bits iter c r t hd hk read history
  · intro h
    simp [compiledTCount, literalProgram_tCount, AdaptiveCircuit.tCount]

end ShorECDLP.Paper2607_13816.ChallengeMigration
