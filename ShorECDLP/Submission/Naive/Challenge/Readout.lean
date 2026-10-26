import ShorECDLP.Challenge.Contract
import ShorECDLP.Framework.Quantum.Measurement

namespace ShorECDLP.NaiveChallenge
open Quantum Challenge
noncomputable section

/-- An explicit computational-basis measurement, encoded with the existing
H followed by X-measure/reset primitives. The result is appended to the tape. -/
def readBit {n start : Nat} (wire : Wire) : Straight n start (start+1) :=
  .gate (.literal (.H wire)) (.measure wire .done)

def zReset (wire : Wire) (outcome : Bool) : State →ₗ[ℂ] State :=
  (Quantum.run (resetCircuit wire outcome)).comp (projectZ wire outcome)

theorem xReset_after_H (wire : Wire) (outcome : Bool) (ψ : State) :
    xResetKraus wire outcome (applyGate (.H wire) ψ) = zReset wire outcome ψ := by
  unfold xResetKraus zReset
  simp only [LinearMap.comp_apply]
  rw [show applyGate (.H wire) (applyGate (.H wire) ψ) = ψ from
    applyGate_adjoint_applyGate (.H wire) trivial ψ]

theorem readBit_instantiate {n start : Nat} (wire : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    (readBit wire).instantiate read history =
      .unitary [.H wire] (.xMeasureReset wire .done .done) := rfl

theorem readBit_wellFormed {n start : Nat} (wire : Wire) :
    (readBit (n := n) (start := start) wire).WellFormed := by
  trivial

theorem readBit_gateSlots {n start : Nat} (wire : Wire) :
    (readBit (n := n) (start := start) wire).gateSlots = 1 := rfl

theorem readBit_measurementCount {n start : Nat} (wire : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((readBit wire).instantiate read history).measurementCount = 1 := rfl

/-- The new readout carries the exact Z-projection probability, including on
superpositions and entangled inputs. Reset introduces no extra loss. -/
theorem zReset_normSq (wire : Wire) (outcome : Bool) (ψ : State) :
    normSq (zReset wire outcome ψ) = normSq (projectZ wire outcome ψ) := by
  apply normSq_run
  cases outcome <;> simp [resetCircuit, CircuitWellFormed, Gate.WellFormed]

theorem zReset_ket (wire : Wire) (outcome : Bool) (s : BasisState) :
    zReset wire outcome (ket s) =
      if s wire = outcome then ket (s[wire ↦ false]) else 0 := by
  simp only [zReset, LinearMap.comp_apply, projectZ_ket]
  split_ifs with h
  · cases outcome with
    | false =>
        have hs : s[wire ↦ false] = s := by
          funext w
          by_cases hw : w = wire
          · subst w; simp [h]
          · simp [upd, hw]
        simp [resetCircuit, hs]
    | true => simp [resetCircuit, onKet, h]
  · simp

def castFinish {n start finish finish' : Nat} (h : finish = finish')
    (p : Straight n start finish) : Straight n start finish' := h ▸ p

@[simp] theorem instantiate_castFinish {n start finish finish' : Nat}
    (h : finish = finish') (p : Straight n start finish)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    (castFinish h p).instantiate read history =
      p.instantiate read history := by
  subst finish'
  rfl

@[simp] theorem wellFormed_castFinish {n start finish finish' : Nat}
    (h : finish = finish') (p : Straight n start finish) :
    (castFinish h p).WellFormed = p.WellFormed := by
  subst finish'
  rfl

@[simp] theorem gateSlots_castFinish {n start finish finish' : Nat}
    (h : finish = finish') (p : Straight n start finish) :
    (castFinish h p).gateSlots = p.gateSlots := by
  subst finish'
  rfl

/-- Fixed wire order, with one appended computational-basis outcome per wire. -/
def readWires {n : Nat} : (wires : List Wire) → (start : Nat) →
    Straight n start (start + wires.length)
  | [], start => by simpa using (Straight.done : Straight n start start)
  | wire :: wires, start => .gate (.literal (.H wire)) (.measure wire
      (castFinish (by simp [Nat.add_comm, Nat.add_left_comm])
        (readWires wires (start+1))))

def zReadout : List Wire → AdaptiveCircuit
  | [] => .done
  | wire :: wires => .unitary [.H wire]
      (.xMeasureReset wire (zReadout wires) (zReadout wires))

theorem readWires_instantiate {n : Nat} (wires : List Wire) (start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    (readWires wires start).instantiate read history = zReadout wires := by
  induction wires generalizing start with
  | nil => rfl
  | cons w ws ih => simp [readWires, Straight.instantiate, TemplateGate.instantiate,
      zReadout, ih]

theorem readWires_wellFormed {n : Nat} (wires : List Wire) (start : Nat) :
    (readWires (n := n) wires start).WellFormed := by
  induction wires generalizing start with
  | nil => trivial
  | cons w ws ih => simp [readWires, Straight.WellFormed, TemplateGate.WellFormed, Gate.WellFormed, ih]

theorem readWires_gateSlots {n : Nat} (wires : List Wire) (start : Nat) :
    (readWires (n := n) wires start).gateSlots = wires.length := by
  induction wires generalizing start with
  | nil => rfl
  | cons w ws ih => simp [readWires, Straight.gateSlots, ih, Nat.add_comm]

theorem readWires_measurementCount {n : Nat} (wires : List Wire) (start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((readWires wires start).instantiate read history).measurementCount = wires.length := by
  rw [Straight.measurementCount]
  omega

/-- This is an actual branch-history length, not only a static resource count. -/
theorem zReadout_history_length (wires : List Wire) (branch : InstrumentBranch)
    (h : branch ∈ (zReadout wires).run) : branch.history.length = wires.length := by
  induction wires generalizing branch with
  | nil =>
      simp [zReadout, AdaptiveCircuit.run] at h
      subst branch
      rfl
  | cons wire wires ih =>
      simp only [zReadout, AdaptiveCircuit.run, List.mem_map, List.mem_append] at h
      obtain ⟨mid, hm, rfl⟩ := h
      rcases hm with hm | hm
      · obtain ⟨prior, hp, rfl⟩ := hm
        change (false :: prior.history).length = (wire :: wires).length
        simp [ih prior hp]
      · obtain ⟨prior, hp, rfl⟩ := hm
        change (true :: prior.history).length = (wire :: wires).length
        simp [ih prior hp]

/-- Both concrete measurement branches have the stated Z-reset Kraus map. -/
theorem readBit_run {n start : Nat} (wire : Wire)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((readBit wire).instantiate read history).run =
      [{ history := [false], kraus := zReset wire false },
       { history := [true], kraus := zReset wire true }] := by
  change ([{ history := [false], kraus := (LinearMap.id.comp (xResetKraus wire false)).comp (Quantum.run [.H wire]) },
    { history := [true], kraus := (LinearMap.id.comp (xResetKraus wire true)).comp (Quantum.run [.H wire]) }] : Instrument) = _
  have h (b : Bool) :
      (LinearMap.id.comp (xResetKraus wire b)).comp (Quantum.run [.H wire]) =
        zReset wire b := by
    apply LinearMap.ext
    intro ψ
    exact xReset_after_H wire b ψ
  rw [h false, h true]

/-- Reset does not change the total probability of the two recorded outcomes. -/
theorem zReset_mass (wire : Wire) (ψ : State) :
    normSq (zReset wire false ψ) + normSq (zReset wire true ψ) = normSq ψ := by
  rw [zReset_normSq, zReset_normSq]
  exact normSq_projectZ_false_add_true wire ψ

/-- Non-destructive computational readout; the fixed newest record controls X. -/
def observeWires {n : Nat} : (wires : List Wire) → (start : Nat) →
    Straight n start (start + wires.length)
  | [], start => by simpa using (Straight.done : Straight n start start)
  | wire :: wires, start => .gate (.literal (.H wire)) (.measure wire
      (.recordGate (Fin.last start) true (.X wire)
        (castFinish (by simp [Nat.add_comm, Nat.add_left_comm])
          (observeWires wires (start+1)))))

def zObserve : List Wire → AdaptiveCircuit
  | [] => .done
  | wire :: wires => .unitary [.H wire] (.xMeasureReset wire
      (.unitary [] (zObserve wires)) (.unitary [.X wire] (zObserve wires)))

theorem observeWires_instantiate {n : Nat} (wires : List Wire) (start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    (observeWires wires start).instantiate read history = zObserve wires := by
  induction wires generalizing start with
  | nil => rfl
  | cons w ws ih =>
      simp [observeWires, Straight.instantiate, TemplateGate.instantiate, zObserve,
        ih, Fin.lastCases_last]

theorem observe_projection (wire : Wire) (b : Bool) (ψ : State) :
    Quantum.run (resetCircuit wire b)
      (xResetKraus wire b (applyGate (.H wire) ψ)) = projectZ wire b ψ := by
  rw [xReset_after_H]
  unfold zReset
  simp only [LinearMap.comp_apply]
  cases b with
  | false => rfl
  | true =>
      exact applyGate_adjoint_applyGate (.X wire) trivial _

/-- Born mass of a predicate on actual measurement records. -/
def recordMass (I : Instrument) (event : List Bool → Bool) (ψ : State) : ℝ :=
  (I.map fun branch => if event branch.history then normSq (branch.kraus ψ) else 0).sum

/-- Classical event weight in the computational basis. -/
def basisMass (event : BasisState → Bool) (ψ : State) : ℝ :=
  ψ.sum fun s a => if event s then Complex.normSq a else 0

theorem normSq_basisMass (ψ : State) : normSq ψ = basisMass (fun _ => true) ψ := by
  classical
  have hinner : inner ψ ψ = ((ψ.sum fun _ a => Complex.normSq a : ℝ) : ℂ) := by
    unfold inner Finsupp.sum
    push_cast
    apply Finset.sum_congr rfl
    intro s _
    exact Complex.normSq_eq_conj_mul_self.symm
  unfold normSq
  rw [hinner]
  simp [basisMass]

theorem basisMass_projectZ (event : BasisState → Bool) (wire : Wire) (b : Bool) (ψ : State) :
    basisMass event (projectZ wire b ψ) =
      basisMass (fun s => decide (s wire = b) && event s) ψ := by
  classical
  unfold basisMass
  rw [projectZ_apply]
  simp [Finsupp.sum, Finsupp.support_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s _
  by_cases h : s wire = b <;> simp [h]

def prependProjection (wire : Wire) (b : Bool) (branch : InstrumentBranch) : InstrumentBranch :=
  ⟨b :: branch.history, branch.kraus.comp (projectZ wire b)⟩

theorem zObserve_run_cons (wire : Wire) (wires : List Wire) :
    (zObserve (wire :: wires)).run =
      (zObserve wires).run.map (prependProjection wire false) ++
      (zObserve wires).run.map (prependProjection wire true) := by
  simp only [zObserve, AdaptiveCircuit.run, List.map_append, List.map_map]
  apply congrArg₂ (· ++ ·)
  · apply List.map_congr_left
    intro branch _
    change ({ history := false :: branch.history, kraus := ((branch.kraus.comp (Quantum.run [])).comp (xResetKraus wire false)).comp (Quantum.run [.H wire]) } : InstrumentBranch) = _
    unfold prependProjection
    congr 1
    apply LinearMap.ext
    intro ψ
    exact congrArg branch.kraus (observe_projection wire false ψ)
  · apply List.map_congr_left
    intro branch _
    change ({ history := true :: branch.history, kraus := ((branch.kraus.comp (Quantum.run [.X wire])).comp (xResetKraus wire true)).comp (Quantum.run [.H wire]) } : InstrumentBranch) = _
    unfold prependProjection
    congr 1
    apply LinearMap.ext
    intro ψ
    exact congrArg branch.kraus (observe_projection wire true ψ)

theorem recordMass_zObserve_cons (event : List Bool → Bool) (wire : Wire)
    (wires : List Wire) (ψ : State) :
    recordMass (zObserve (wire :: wires)).run event ψ =
      recordMass (zObserve wires).run (fun bits => event (false :: bits)) (projectZ wire false ψ) +
      recordMass (zObserve wires).run (fun bits => event (true :: bits)) (projectZ wire true ψ) := by
  rw [zObserve_run_cons]
  simp [recordMass, List.map_append, List.map_map, prependProjection, Function.comp_def]

theorem recordMass_zObserve (wires : List Wire) (event : List Bool → Bool) (ψ : State) :
    recordMass (zObserve wires).run event ψ =
      basisMass (fun s => event (wires.map s)) ψ := by
  classical
  induction wires generalizing event ψ with
  | nil =>
      simp only [zObserve, AdaptiveCircuit.run, recordMass, List.map_cons, List.map_nil,
        LinearMap.id_apply, List.sum_cons, List.sum_nil, add_zero]
      cases h : event []
      · simp [basisMass]
      · simpa [basisMass] using normSq_basisMass ψ
  | cons wire wires ih =>
      rw [recordMass_zObserve_cons, ih, ih, basisMass_projectZ, basisMass_projectZ]
      unfold basisMass Finsupp.sum
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro s _
      cases hbit : s wire <;> simp [hbit]

def bitsValue : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * bitsValue bs

theorem bitsValue_map (wires : List Wire) (s : BasisState) :
    bitsValue (wires.map s) = regValue wires s := by
  induction wires with
  | nil => rfl
  | cons w ws ih => simp [bitsValue, regValue, ih]

def jointRecordEvent (leftWidth a b : Nat) (bits : List Bool) : Bool :=
  decide (bitsValue (bits.take leftWidth) = a ∧ bitsValue (bits.drop leftWidth) = b)

/-- Exact joint probability of the two actually recorded registers, for every
input state, including entangled states. No independence assumption is used. -/
theorem zObserve_jointProbability (aReg bReg : List Wire) (a b : Nat) (ψ : State) :
    recordMass (zObserve (aReg ++ bReg)).run (jointRecordEvent aReg.length a b) ψ =
      Quantum.OrderFinding.jointRegisterProbability aReg bReg a b ψ := by
  classical
  rw [recordMass_zObserve]
  unfold basisMass Finsupp.sum Quantum.OrderFinding.jointRegisterProbability
  apply Finset.sum_congr rfl
  intro s _
  simp [jointRecordEvent, bitsValue_map]

theorem observeWires_jointProbability {n : Nat} (aReg bReg : List Wire) (a b start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) (ψ : State) :
    recordMass ((observeWires (aReg ++ bReg) start).instantiate read history).run
      (jointRecordEvent aReg.length a b) ψ =
      Quantum.OrderFinding.jointRegisterProbability aReg bReg a b ψ := by
  rw [observeWires_instantiate]
  exact zObserve_jointProbability aReg bReg a b ψ

end
end ShorECDLP.NaiveChallenge
