import ShorECDLP.Submission.Naive.Challenge.Static

namespace ShorECDLP.NaiveChallenge
open Quantum Challenge

def slotGate {n : Nat} : TemplateGate n → Gate
  | .literal g => g
  | .whenBit _ _ g => g

def straightWires {n s e : Nat} : Straight n s e → List Wire
  | .done => []
  | .gate g p => gateWires (slotGate g) ++ straightWires p
  | .recordGate _ _ g p => gateWires g ++ straightWires p
  | .measure w p => w :: straightWires p

def straightT {n s e : Nat} : Straight n s e → Nat
  | .done => 0
  | .gate g p => tCost (slotGate g) + straightT p
  | .recordGate _ _ g p => tCost g + straightT p
  | .measure _ p => straightT p

theorem slot_wires_subset {n : Nat} (g : TemplateGate n) (read : ConstantBit n → Bool) :
    circuitWires (g.instantiate read) ⊆ gateWires (slotGate g) := by
  cases g with
  | literal g => simp [TemplateGate.instantiate, slotGate, circuitWires]
  | whenBit r b g =>
    simp only [TemplateGate.instantiate]
    split <;> simp [slotGate, circuitWires]

theorem straight_wires_subset {n s e : Nat} (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    (p.instantiate read history).wires ⊆ straightWires p := by
  induction p with
  | done => exact List.Subset.refl _
  | gate g p ih =>
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact List.mem_append_left _ (slot_wires_subset g read hw)
    · exact List.mem_append_right _ (ih history hw)
  | recordGate r b g p ih =>
    simp only [Straight.instantiate, AdaptiveCircuit.wires, straightWires]
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · apply List.mem_append_left
      split at hw
      · simpa only [circuitWires, List.flatMap_cons, List.flatMap_nil, List.append_nil] using hw
      · exact False.elim (List.not_mem_nil hw)
    · exact List.mem_append_right _ (ih history hw)
  | measure w p ih =>
    intro v hv
    simp only [Straight.instantiate, AdaptiveCircuit.wires, List.mem_cons, List.mem_append] at hv
    rcases hv with rfl | hv | hv
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih _ hv)
    · exact List.mem_cons_of_mem _ (ih _ hv)

theorem straight_qubit_bound {n s e : Nat} (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    (p.instantiate read history).qubitCount ≤ (straightWires p).dedup.length := by
  have hs : (p.instantiate read history).wires.toFinset ⊆ (straightWires p).toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (straight_wires_subset p read history (List.mem_toFinset.mp hw))
  simpa only [AdaptiveCircuit.qubitCount, List.card_toFinset] using Finset.card_le_card hs

theorem slot_t_bound {n : Nat} (g : TemplateGate n) (read : ConstantBit n → Bool) :
    ShorECDLP.tCount (g.instantiate read) ≤ tCost (slotGate g) := by
  cases g with
  | literal g => simp [TemplateGate.instantiate, slotGate, ShorECDLP.tCount]
  | whenBit r b g =>
    simp only [TemplateGate.instantiate]
    split <;> simp [slotGate, ShorECDLP.tCount]

theorem straight_t_bound {n s e : Nat} (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    (p.instantiate read history).tCount ≤ straightT p := by
  induction p with
  | done => exact Nat.le_refl _
  | gate g p ih => exact Nat.add_le_add (slot_t_bound g read) (ih history)
  | recordGate r b g p ih =>
    simp only [Straight.instantiate, AdaptiveCircuit.tCount, straightT]
    apply Nat.add_le_add _ (ih history)
    split <;> simp [ShorECDLP.tCount]
  | measure w p ih => exact max_le (ih _) (ih _)

/-- Closed bounds computed from all submitted slots, independent of Q. -/
def observedStaticBounds : Bounds :=
  ⟨(straightWires (observedTrialProgram 0)).dedup.length,
    straightT (observedTrialProgram 0), 512⟩

theorem observedTrialProgram_resources (Q : Secp256k1.Point) :
    (resources ((observedTrialProgram 0).instantiate (readConstant naivePowerCoefficient Q)
      (fun i => Fin.elim0 i))).qubits ≤ observedStaticBounds.qubits ∧
    (resources ((observedTrialProgram 0).instantiate (readConstant naivePowerCoefficient Q)
      (fun i => Fin.elim0 i))).tModel ≤ observedStaticBounds.tModel ∧
    (resources ((observedTrialProgram 0).instantiate (readConstant naivePowerCoefficient Q)
      (fun i => Fin.elim0 i))).measurements = 512 := by
  dsimp only [resources, observedStaticBounds]
  refine ⟨straight_qubit_bound (observedTrialProgram 0) (readConstant naivePowerCoefficient Q)
    (fun i => Fin.elim0 i), straight_t_bound (observedTrialProgram 0)
    (readConstant naivePowerCoefficient Q) (fun i => Fin.elim0 i), ?_⟩
  change ((observedTrialProgram 0).instantiate _ _).measurementCount = 512
  rw [Straight.measurementCount]
  simp only [List.length_append, Secp256k1.bitcoinAReg, Secp256k1.bitcoinBReg, List.length_range']

theorem observeWires_slots {n : Nat} (ws : List Wire) (cursor : Nat) :
    (observeWires (n := n) ws cursor).gateSlots = 2 * ws.length := by
  induction ws generalizing cursor with
  | nil => rfl
  | cons w ws ih =>
    simp only [observeWires, Straight.gateSlots, gateSlots_castFinish, ih, List.length_cons]
    omega

theorem observedGateProgram_slots {n : Nat} (gs : List (TemplateGate n)) (ws : List Wire)
    (cursor : Nat) :
    ((constantGateProgram gs cursor).append (observeWires ws cursor)).gateSlots =
      gs.length + 2 * ws.length := by
  rw [Straight.gateSlots_append, constantGateProgram_slots, observeWires_slots]

theorem observedTrialProgram_slots (cursor : Nat) :
    (observedTrialProgram cursor).gateSlots = trialGates.length + 1024 := by
  have h := observedGateProgram_slots trialGates (Secp256k1.bitcoinAReg ++ Secp256k1.bitcoinBReg) cursor
  have hl : 2 * (Secp256k1.bitcoinAReg ++ Secp256k1.bitcoinBReg).length = 1024 := by
    simp only [List.length_append, Secp256k1.bitcoinAReg, Secp256k1.bitcoinBReg, List.length_range']
  exact h.trans (congrArg (fun k => trialGates.length + k) hl)

end ShorECDLP.NaiveChallenge
