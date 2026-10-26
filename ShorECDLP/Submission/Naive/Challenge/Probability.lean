import ShorECDLP.Submission.Naive.Challenge.Readout
namespace ShorECDLP.NaiveChallenge
open Quantum
open scoped BigOperators
noncomputable section
private theorem regValue_bound (ws : List Wire) (s : BasisState) :
    regValue ws s < 2 ^ ws.length := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
      rw [regValue_cons, List.length_cons, Nat.pow_succ]
      by_cases h : s w <;> simp [h] <;> omega

theorem jointProbability_event (aReg bReg : List Wire) (precision : Nat)
    (ha : aReg.length = precision) (hb : bReg.length = precision)
    (event : Nat → Nat → Bool) (ψ : State) :
    (∑ a : Fin (2^precision), ∑ b : Fin (2^precision),
      if event a.val b.val then
        Quantum.OrderFinding.jointRegisterProbability aReg bReg a.val b.val ψ else 0) =
      basisMass (fun s => event (regValue aReg s) (regValue bReg s)) ψ := by
  classical
  unfold Quantum.OrderFinding.jointRegisterProbability basisMass Finsupp.sum
  have hexpand (a b : Fin (2^precision)) :
      (if event a.val b.val then
        ∑ s ∈ ψ.support, if regValue aReg s = a.val ∧ regValue bReg s = b.val
          then Complex.normSq (ψ s) else 0 else 0) =
      ∑ s ∈ ψ.support, if regValue aReg s = a.val ∧ regValue bReg s = b.val
        then (if event a.val b.val then Complex.normSq (ψ s) else 0) else 0 := by
    cases event a.val b.val <;> simp
  simp_rw [hexpand]
  calc
    _ = ∑ a : Fin (2^precision), ∑ s ∈ ψ.support, ∑ b : Fin (2^precision),
      if regValue aReg s = a.val ∧ regValue bReg s = b.val
        then (if event a.val b.val then Complex.normSq (ψ s) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ s ∈ ψ.support, ∑ a : Fin (2^precision), ∑ b : Fin (2^precision),
      if regValue aReg s = a.val ∧ regValue bReg s = b.val
        then (if event a.val b.val then Complex.normSq (ψ s) else 0) else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      let a : Fin (2^precision) := ⟨regValue aReg s, by simpa [ha] using regValue_bound aReg s⟩
      let b : Fin (2^precision) := ⟨regValue bReg s, by simpa [hb] using regValue_bound bReg s⟩
      rw [Finset.sum_eq_single a]
      · rw [Finset.sum_eq_single b]
        · simp [a, b]
        · intro b' _ hne
          have hbval : regValue bReg s ≠ b'.val := by
            intro h
            exact hne (Fin.ext h.symm)
          simp [hbval]
        · simp
      · intro a' _ hne
        have haval : regValue aReg s ≠ a'.val := by
          intro h
          exact hne (Fin.ext h.symm)
        simp [haval]
      · simp

def pairEvent (leftWidth : Nat) (event : Nat → Nat → Bool) (bits : List Bool) : Bool :=
  event (bitsValue (bits.take leftWidth)) (bitsValue (bits.drop leftWidth))

theorem zObserve_eventProbability (aReg bReg : List Wire) (precision : Nat)
    (ha : aReg.length = precision) (hb : bReg.length = precision)
    (event : Nat → Nat → Bool) (ψ : State) :
    recordMass (zObserve (aReg ++ bReg)).run (pairEvent aReg.length event) ψ =
    ∑ a : Fin (2^precision), ∑ b : Fin (2^precision),
      if event a.val b.val then
        Quantum.OrderFinding.jointRegisterProbability aReg bReg a.val b.val ψ else 0 := by
  rw [recordMass_zObserve, jointProbability_event aReg bReg precision ha hb]
  simp [pairEvent, bitsValue_map]
theorem recordMass_filter (I : Instrument) (event : List Bool → Bool) (ψ : State) :
    recordMass I event ψ = Instrument.bornMass (I.filter (fun b => event b.history)) ψ := by
  induction I with
  | nil => rfl
  | cons b I ih => cases h : event b.history <;> simp [recordMass, Instrument.bornMass, h] at * <;> exact ih

theorem zObserve_wellFormed (wires : List Wire) : (zObserve wires).WellFormed := by
  induction wires with
  | nil => trivial
  | cons w ws ih =>
      exact ⟨by simp [CircuitWellFormed, Gate.WellFormed],
        ⟨⟨by simp [CircuitWellFormed], ih⟩, ⟨by simp [CircuitWellFormed, Gate.WellFormed], ih⟩⟩⟩

theorem zObserve_history_length (wires : List Wire) (b : InstrumentBranch)
    (hb : b ∈ (zObserve wires).run) : b.history.length = wires.length := by
  induction wires generalizing b with
  | nil => simp [zObserve, AdaptiveCircuit.run] at hb; subst b; rfl
  | cons w ws ih =>
      rw [zObserve_run_cons] at hb
      rcases List.mem_append.mp hb with hb | hb
      · obtain ⟨prior, hp, rfl⟩ := List.mem_map.mp hb
        simp [prependProjection, ih prior hp]
      · obtain ⟨prior, hp, rfl⟩ := List.mem_map.mp hb
        simp [prependProjection, ih prior hp]

def observedTrial (c : Circuit) (aReg bReg : List Wire) : AdaptiveCircuit :=
  .unitary c (zObserve (aReg ++ bReg))

theorem observedTrial_history_length (c : Circuit) (aReg bReg : List Wire)
    (b : InstrumentBranch) (hb : b ∈ (observedTrial c aReg bReg).run) :
    b.history.length = aReg.length + bReg.length := by
  obtain ⟨prior, hp, rfl⟩ := List.mem_map.mp hb
  simpa using zObserve_history_length (aReg ++ bReg) prior hp

theorem observedTrial_recordMass (c : Circuit) (aReg bReg : List Wire)
    (event : List Bool → Bool) (ψ : State) :
    recordMass (observedTrial c aReg bReg).run event ψ =
      recordMass (zObserve (aReg ++ bReg)).run event (Quantum.run c ψ) := by
  simp only [observedTrial, AdaptiveCircuit.run, recordMass, List.map_map]
  rfl

theorem observedTrial_total (c : Circuit) (aReg bReg : List Wire) (ψ : State) :
    (observedTrial c aReg bReg).run.bornMass ψ = normSq (Quantum.run c ψ) := by
  have h := AdaptiveCircuit.run_preservesBornMass _
    (zObserve_wellFormed (aReg ++ bReg)) (Quantum.run c ψ)
  simpa only [observedTrial, AdaptiveCircuit.run, Instrument.bornMass, List.map_map] using h

end
end ShorECDLP.NaiveChallenge
