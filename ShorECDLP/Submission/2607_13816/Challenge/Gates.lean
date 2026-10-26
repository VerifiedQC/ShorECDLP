import ShorECDLP.Challenge.StraightLine

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

/-- A fixed list of optional primitive gates, with no measurements or callbacks. -/
def gateProgram {n cursor : Nat} : List (TemplateGate n) → Straight n cursor cursor
  | [] => .done
  | g :: gs => .gate g (gateProgram gs)

theorem gateProgram_slots {n cursor : Nat} (gs : List (TemplateGate n)) :
    (gateProgram (cursor := cursor) gs).gateSlots = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [gateProgram, Straight.gateSlots, ih, Nat.add_comm]

theorem gateProgram_run {n cursor : Nat} (gs : List (TemplateGate n))
    (read : ConstantBit n → Bool) (history : Fin cursor → Bool) :
    ((gateProgram gs).instantiate read history).run =
      (AdaptiveCircuit.unitary (gs.flatMap (TemplateGate.instantiate read)) .done).run := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [gateProgram, Straight.instantiate, AdaptiveCircuit.run, ih, List.flatMap_cons]
    simp [Quantum.run_append_map]
    rfl

/-- A lookup leaf lists every possible target, even when its constant bit is zero. -/
def lookupLeafGates {n : Nat} (control : Wire) (ports : List (ConstantBit n × Wire)) :
    List (TemplateGate n) :=
  ports.map (fun p => .whenBit p.1 true (.CX control p.2))

theorem lookupLeafGates_instantiate {n : Nat} (control : Wire)
    (ports : List (ConstantBit n × Wire)) (read : ConstantBit n → Bool) :
    (lookupLeafGates control ports).flatMap (TemplateGate.instantiate read) =
      ((ports.filter (fun p => read p.1)).map (fun p => Gate.CX control p.2)) := by
  induction ports with
  | nil => rfl
  | cons p ps ih =>
    cases h : read p.1 <;>
      simp [lookupLeafGates, TemplateGate.instantiate, h, lookupLeafGates] at ih ⊢ <;>
      exact ih

theorem lookupLeaf_slots {n cursor : Nat} (control : Wire)
    (ports : List (ConstantBit n × Wire)) :
    (gateProgram (cursor := cursor) (lookupLeafGates control ports)).gateSlots = ports.length := by
  simp [gateProgram_slots, lookupLeafGates]

end ShorECDLP.Paper2607_13816.ChallengeMigration
