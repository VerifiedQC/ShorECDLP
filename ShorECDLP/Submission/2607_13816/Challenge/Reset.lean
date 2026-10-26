import ShorECDLP.Challenge.StraightLine
import ShorECDLP.Framework.Quantum.MeasurementUncompute

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

/-- Fixed wire order, independent of coordinates and all measurement outcomes. -/
def resetWires : List Wire := List.range 837 ++ [838] ++ List.range' 855 16

theorem resetWires_length : resetWires.length = 854 := by
  simp [resetWires]

def castFinish {n s e f : Nat} (h : e = f) (p : Straight n s e) : Straight n s f := h ▸ p

@[simp] theorem castFinish_gateSlots {n s e f : Nat} (h : e = f) (p : Straight n s e) :
    (castFinish h p).gateSlots = p.gateSlots := by subst f; rfl

/-- Reset a statically supplied register, retaining chronological records. -/
def resetProgram (n start : Nat) : (ws : List Wire) → Straight n start (start + ws.length)
  | [] => .done
  | w :: ws => castFinish (by simp [Nat.add_comm, Nat.add_left_comm])
      (.measure w (resetProgram n (start + 1) ws))

theorem resetProgram_gateSlots (n start : Nat) (ws : List Wire) :
    (resetProgram n start ws).gateSlots = 0 := by
  induction ws generalizing start with
  | nil => rfl
  | cons w ws ih => simpa [resetProgram, Straight.gateSlots] using ih (start + 1)

@[simp] theorem castFinish_instantiate {n s e f : Nat} (h : e = f)
    (p : Straight n s e) (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    (castFinish h p).instantiate read history = p.instantiate read history := by
  subst f; rfl

/-- Exact instrument equality, including all recorded outcomes. -/
theorem resetProgram_run (n start : Nat) (ws : List Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((resetProgram n start ws).instantiate read history).run =
      (measureResetWithCorrection ws (fun _ => [])).run := by
  induction ws generalizing start with
  | nil => simp [resetProgram, Straight.instantiate, measureResetWithCorrection,
      AdaptiveCircuit.run, Quantum.run]
  | cons w ws ih =>
    simp only [resetProgram, castFinish_instantiate, Straight.instantiate,
      measureResetWithCorrection, AdaptiveCircuit.run]
    rw [ih, ih]

def fixedReset (n start : Nat) : Straight n start (start + 854) :=
  castFinish (by rw [resetWires_length]) (resetProgram n start resetWires)

theorem fixedReset_gateSlots (n start : Nat) : (fixedReset n start).gateSlots = 0 := by
  simp [fixedReset, resetProgram_gateSlots]

theorem fixedReset_measurements (n start : Nat) (read : ConstantBit n → Bool)
    (history : Fin start → Bool) :
    ((fixedReset n start).instantiate read history).measurementCount = 854 := by
  rw [Straight.measurementCount]; omega

theorem fixedReset_run (n start : Nat) (read : ConstantBit n → Bool)
    (history : Fin start → Bool) :
    ((fixedReset n start).instantiate read history).run =
      (measureResetWithCorrection resetWires (fun _ => [])).run := by
  simp only [fixedReset, castFinish_instantiate, resetProgram_run]

end ShorECDLP.Paper2607_13816.ChallengeMigration
