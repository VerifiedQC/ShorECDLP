import ShorECDLP.Submission.«2607_13816».Challenge.GidneyCompare
import ShorECDLP.Submission.«2607_13816».Arithmetic.ModularAdd

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

def appendCompiled {n start : Nat} (p : (count : Nat) × Straight n start (start+count))
    (q : (count : Nat) × Straight n (start+p.1) (start+p.1+count)) :
    (count : Nat) × Straight n start (start+count) :=
  ⟨p.1+q.1, castFinish (Nat.add_assoc start p.1 q.1) (p.2.append q.2)⟩

theorem appendCompiled_run {n start : Nat} (p : (count : Nat) × Straight n start (start+count))
    (q : (count : Nat) × Straight n (start+p.1) (start+p.1+count))
    (read : ConstantBit n → Bool) (history : Fin start → Bool) (target : AdaptiveCircuit)
    (hq : ∀ h, compiledRun q read h = target.run) :
    compiledRun (appendCompiled p q) read history = ((p.2.instantiate read history).seq target).run := by
  simp only [appendCompiled, compiledRun, castFinish_instantiate]
  exact append_run_fixed p.2 q.2 read history target hq

def modularAddProgram (n start : Nat) (input acc : List Wire) (correction : List Bool)
    (modulus : Nat) (q carry spare ancilla flag : Wire) :
    (count : Nat) × Straight n start (start+count) :=
  let compare := uncontrolledCompareProgram n start acc input modulus carry spare ancilla flag
  let add := gidneyProgram n (start+compare.1) acc (input.take (acc.length-1)) correction flag carry spare ancilla
  let middle := appendCompiled compare
    ⟨add.1, add.2.append (literalProgram (controlledCompareLT acc input q carry flag))⟩
  ⟨middle.1, (literalProgram (controlledAddCarry input acc q carry flag)).append middle.2⟩

theorem modularAddProgram_run (n start : Nat) (input acc : List Wire) (correction : List Bool)
    (modulus : Nat) (q carry spare ancilla flag : Wire)
    (hl : input.length = acc.length) (hk : correction.length = acc.length) (hpos : 0 < acc.length)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (modularAddProgram n start input acc correction modulus q carry spare ancilla flag) read history =
      (controlledModularAdd input acc correction modulus q carry spare ancilla flag).run := by
  have hd : acc.length = (input.take (acc.length-1)).length + 1 := by
    rw [List.length_take, hl, Nat.min_eq_left (by omega)]
    omega
  let compare := uncontrolledCompareProgram n start acc input modulus carry spare ancilla flag
  let add := gidneyProgram n (start+compare.1) acc (input.take (acc.length-1)) correction flag carry spare ancilla
  have addRun : ∀ h, (add.2.instantiate read h).run =
      (controlledGidneyAddConst acc (input.take (acc.length-1)) correction flag carry spare ancilla).run :=
    fun h => gidneyProgram_run n _ acc _ correction flag carry spare ancilla hd hk read h
  have tailRun : ∀ h, compiledRun
      (⟨add.1, add.2.append (literalProgram (controlledCompareLT acc input q carry flag))⟩ :
        (count : Nat) × Straight n (start+compare.1) (start+compare.1+count)) read h =
      ((controlledGidneyAddConst acc (input.take (acc.length-1)) correction flag carry spare ancilla).seq
        (.unitary (controlledCompareLT acc input q carry flag) .done)).run := by
    intro h
    simp only [compiledRun]
    rw [append_run_fixed _ _ _ _ _ (fun h => literalProgram_run _ read h),
      AdaptiveCircuit.run_seq, addRun h, ← AdaptiveCircuit.run_seq]
  change (((literalProgram (controlledAddCarry input acc q carry flag)).append
    (appendCompiled compare ⟨add.1, add.2.append (literalProgram (controlledCompareLT acc input q carry flag))⟩).2).instantiate read history).run = _
  rw [literalProgram_append_run]
  simp only [AdaptiveCircuit.run]
  rw [show ((appendCompiled compare ⟨add.1, add.2.append (literalProgram (controlledCompareLT acc input q carry flag))⟩).2.instantiate read history).run = _ from
    appendCompiled_run compare _ read history _ tailRun]
  have compareRun : (compare.2.instantiate read history).run =
      (gidneyCompareGE acc input modulus carry spare ancilla flag).run :=
    uncontrolledCompareProgram_run n start acc input modulus carry spare ancilla flag hl.symm read history
  rw [AdaptiveCircuit.run_seq, compareRun, ← AdaptiveCircuit.run_seq]
  rfl

theorem literalProgram_tCount {n start : Nat} (gs : Circuit)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((literalProgram gs).instantiate read history).tCount = ShorECDLP.tCount gs := by
  rw [literalProgram, gateProgram_tCount, literal_gates]

theorem appendCompiled_tCount {n start : Nat} (p : (count : Nat) × Straight n start (start+count))
    (q : (count : Nat) × Straight n (start+p.1) (start+p.1+count))
    (read : ConstantBit n → Bool) (history : Fin start → Bool) (m : Nat)
    (hq : ∀ h, compiledTCount q read h = m) :
    compiledTCount (appendCompiled p q) read history = (p.2.instantiate read history).tCount + m := by
  simp only [appendCompiled, compiledTCount, castFinish_instantiate]
  exact append_tCount_fixed p.2 q.2 read history m hq

theorem modularAddProgram_tCount (n start : Nat) (input acc : List Wire) (correction : List Bool)
    (modulus : Nat) (q carry spare ancilla flag : Wire)
    (hl : input.length = acc.length) (hk : correction.length = acc.length) (hpos : 0 < acc.length)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledTCount (modularAddProgram n start input acc correction modulus q carry spare ancilla flag) read history =
      (controlledModularAdd input acc correction modulus q carry spare ancilla flag).tCount := by
  have hd : acc.length = (input.take (acc.length-1)).length + 1 := by
    rw [List.length_take, hl, Nat.min_eq_left (by omega)]
    omega
  let compare := uncontrolledCompareProgram n start acc input modulus carry spare ancilla flag
  let add := gidneyProgram n (start+compare.1) acc (input.take (acc.length-1)) correction flag carry spare ancilla
  have addT : ∀ h, (add.2.instantiate read h).tCount =
      (controlledGidneyAddConst acc (input.take (acc.length-1)) correction flag carry spare ancilla).tCount :=
    fun h => gidneyProgram_tCount n _ acc _ correction flag carry spare ancilla hd hk read h
  have tailT : ∀ h, compiledTCount
      (⟨add.1, add.2.append (literalProgram (controlledCompareLT acc input q carry flag))⟩ :
        (count : Nat) × Straight n (start+compare.1) (start+compare.1+count)) read h =
      (controlledGidneyAddConst acc (input.take (acc.length-1)) correction flag carry spare ancilla).tCount +
        ShorECDLP.tCount (controlledCompareLT acc input q carry flag) := by
    intro h
    simp only [compiledTCount]
    rw [append_tCount_fixed _ _ _ _ _ (fun h => literalProgram_tCount _ read h), addT h]
  change (((literalProgram (controlledAddCarry input acc q carry flag)).append
    (appendCompiled compare ⟨add.1, add.2.append (literalProgram (controlledCompareLT acc input q carry flag))⟩).2).instantiate read history).tCount = _
  rw [literalProgram_append_tCount]
  rw [show ((appendCompiled compare ⟨add.1, add.2.append (literalProgram (controlledCompareLT acc input q carry flag))⟩).2.instantiate read history).tCount = _ from
    appendCompiled_tCount compare _ read history _ tailT]
  have compareT : (compare.2.instantiate read history).tCount =
      (gidneyCompareGE acc input modulus carry spare ancilla flag).tCount :=
    uncontrolledCompareProgram_tCount n start acc input modulus carry spare ancilla flag hl.symm read history
  rw [compareT]
  simp [controlledModularAdd, AdaptiveCircuit.tCount, adaptive_tCount_seq]

theorem modularAddProgram_records (n start : Nat) (input acc : List Wire) (correction : List Bool)
    (modulus : Nat) (q carry spare ancilla flag : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ compiledRun (modularAddProgram n start input acc correction modulus q carry spare ancilla flag) read history) :
    b.history.length = (modularAddProgram n start input acc correction modulus q carry spare ancilla flag).1 := by
  have h := straight_history_length
    (modularAddProgram n start input acc correction modulus q carry spare ancilla flag).2 read history b hb
  simpa using h

end ShorECDLP.Paper2607_13816.ChallengeMigration
