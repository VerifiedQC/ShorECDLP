import ShorECDLP.Submission.Naive.Challenge.Physical
namespace ShorECDLP.NaiveChallenge
open Classical Quantum Secp256k1 Challenge
noncomputable section

def fixedResetWires : List Wire := List.range bitcoinQubitCount

theorem naive_program_value (Q : Point) : bitcoinECDLPSubmission.program Q =
    ecdlpTrial bitcoinAReg bitcoinBReg bitcoinPointReg bitcoinWorkStart bitcoinQFTAncilla Q := by
  unfold bitcoinECDLPSubmission
  rcases bitcoinWireLayout with ⟨ha, hb, hp, hn, hf⟩
  rfl

theorem zObserve_support (ws : List Wire) : (zObserve ws).wires ⊆ ws := by
  induction ws with
  | nil => exact List.Subset.refl _
  | cons w ws ih =>
      intro v hv
      simp only [zObserve, AdaptiveCircuit.wires, circuitWires, gateWires,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | hv | rfl | hv
      all_goals first | exact List.mem_cons_self | exact List.mem_cons_of_mem _ (ih hv)

theorem naiveObserved_fixed_support (Q : Point) :
    (naiveObserved Q).wires ⊆ fixedResetWires := by
  intro w hw
  change w ∈ circuitWires (bitcoinECDLPSubmission.program Q) ++
    (zObserve (bitcoinAReg ++ bitcoinBReg)).wires at hw
  rcases List.mem_append.mp hw with hc | hm
  · rw [naive_program_value] at hc
    exact bitcoinECDLPTrial_fixed_support Q hc
  · have hm := zObserve_support _ hm
    rcases List.mem_append.mp hm with ha | hb
    · simpa [fixedResetWires, bitcoinQubitCount] using
        (show w < 206624 from by
          have := (List.mem_range'_1.mp ha).2
          change w < 0 + 256 at this
          exact this.trans (by decide))
    · simpa [fixedResetWires, bitcoinQubitCount] using
        (show w < 206624 from by
          have := (List.mem_range'_1.mp hb).2
          change w < 256 + 256 at this
          exact this.trans (by decide))

def fixedResetTrial (Q : Point) : AdaptiveCircuit :=
  (naiveObserved Q).seq (resetAll fixedResetWires)
def fixedRepeated (Q : Point) : AdaptiveCircuit := repeatFixed (fixedResetTrial Q) 26
def fixedRepeatedSuccess (d : Nat) (history : List Bool) : Bool :=
  !repeatFailed 207136 (fun bits => naiveEvent d (bits.take 512)) 26 history

theorem fixedResetTrial_support (Q : Point) : (fixedResetTrial Q).wires ⊆ fixedResetWires := by
  intro w hw
  rw [fixedResetTrial, wires_seq] at hw
  rcases hw with hw | hw
  · exact naiveObserved_fixed_support Q hw
  · exact resetAll_support _ hw

theorem fixedResetTrial_zero (Q : Point) (b : InstrumentBranch)
    (hb : b ∈ (fixedResetTrial Q).run) :
    b.kraus (ket zeroBasisState) = (b.kraus (ket zeroBasisState)) zeroBasisState • ket zeroBasisState := by
  have hc : SupportedOn (Clean fixedResetWires) (b.kraus (ket zeroBasisState)) := by
    rw [fixedResetTrial, AdaptiveCircuit.run_seq] at hb
    obtain ⟨before, _, hb⟩ := List.mem_flatMap.mp hb
    obtain ⟨after, ha, rfl⟩ := List.mem_map.mp hb
    exact resetAll_clean _ List.nodup_range after ha (before.kraus (ket zeroBasisState))
  have hs : SupportedOn (fun s => s = zeroBasisState) (b.kraus (ket zeroBasisState)) := by
    intro s hs
    funext w
    by_cases hw : w ∈ fixedResetWires
    · exact hc s hs w hw
    · exact AdaptiveCircuit.branch_frame (fixedResetTrial Q) w false
        (fun h => hw (fixedResetTrial_support Q h)) b hb (ket zeroBasisState)
        (supportedOn_ket _ _ rfl) s hs
  ext s
  by_cases he : s = zeroBasisState
  · subst s; simp [ket]
  · have hz : (b.kraus (ket zeroBasisState)) s = 0 := by
      by_contra h
      exact he (hs s h)
    simp only [ket] at hz
    simp [ket, he, hz]

theorem fixedResetTrial_length (Q : Point) (b : InstrumentBranch)
    (hb : b ∈ (fixedResetTrial Q).run) : b.history.length = 207136 := by
  rw [fixedResetTrial, AdaptiveCircuit.run_seq] at hb
  obtain ⟨before, hbefore, hb⟩ := List.mem_flatMap.mp hb
  obtain ⟨after, hafter, rfl⟩ := List.mem_map.mp hb
  simp only [InstrumentBranch.seq, List.length_append,
    naiveObserved_length Q before hbefore, resetAll_history_length _ after hafter]
  simp [fixedResetWires, bitcoinQubitCount]

theorem fixedResetTrial_total (Q : Point) (d : Nat) (hQ : Q = d • G) (hn : Q ≠ 0) :
    (fixedResetTrial Q).run.bornMass (ket zeroBasisState) = 1 := by
  rw [fixedResetTrial, AdaptiveCircuit.run_seq,
    instrumentMass_seq_preserving _ _ _ (resetAll_mass _), naiveObserved_total Q d hQ hn]

theorem fixedResetTrial_eventMass (Q : Point) (event : List Bool → Bool) (ψ : State) :
    Instrument.bornMass ((fixedResetTrial Q).run.filter
      (fun b => event (b.history.take 512))) ψ =
    Instrument.bornMass ((naiveObserved Q).run.filter (fun b => event b.history)) ψ := by
  rw [fixedResetTrial, AdaptiveCircuit.run_seq]
  rw [instrumentFilter_seq_first _ _ (fun b => event b.history) _ (by
    intro b hb c _
    simp [InstrumentBranch.seq, ← naiveObserved_length Q b hb])]
  exact instrumentMass_seq_preserving _ _ _ (resetAll_mass _)

theorem fixedRepeated_probability (Q : Point) (d : Nat) (hQ : Q = d • G) (hn : Q ≠ 0) :
    Instrument.bornMass ((fixedRepeated Q).run.filter
      (fun b => fixedRepeatedSuccess d b.history)) (ket zeroBasisState) =
      independentRetrySuccessProbability
        (recordMass (naiveObserved Q).run (naiveEvent d) (ket zeroBasisState)) 26 := by
  unfold fixedRepeated fixedRepeatedSuccess
  rw [repeatFixedSuccess_mass _ _ _ (fixedResetTrial_length Q)
    (fixedResetTrial_zero Q) (fixedResetTrial_total Q d hQ hn)]
  rw [fixedResetTrial_eventMass, recordMass_filter]

theorem fixedRepeated_success (Q : Point) (d : Nat) (hQ : Q = d • G) (hn : Q ≠ 0) :
    (99 / 100 : ℝ) ≤ Instrument.bornMass ((fixedRepeated Q).run.filter
      (fun b => fixedRepeatedSuccess d b.history)) (ket zeroBasisState) := by
  rw [fixedRepeated_probability Q d hQ hn]
  have hp := naiveObserved_success Q d hQ hn
  calc
    (99 / 100 : ℝ) ≤ independentRetrySuccessProbability (41 / 250) 26 :=
      by simpa [independentRetrySuccessProbability, naive_bound_value, naive_trialCount_value] using
        bitcoinECDLPSubmission.trialCount_correct
    _ ≤ _ := independentRetrySuccessProbability_mono 26 hp.2 hp.1
/-- The reset suffix contains only fixed-address measurement instructions. -/
def resetWireProgram {n : Nat} : (ws : List Wire) → (start : Nat) → Straight n start (start + ws.length)
  | [], start => by simpa using (Straight.done : Straight n start start)
  | w :: ws, start => .measure w (castFinish
      (by simp [Nat.add_comm, Nat.add_left_comm]) (resetWireProgram ws (start+1)))

def resetNative : List Wire → AdaptiveCircuit
  | [] => .done
  | w :: ws => .xMeasureReset w (resetNative ws) (resetNative ws)

theorem resetWireProgram_instantiate {n : Nat} (ws : List Wire) (start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    (resetWireProgram ws start).instantiate read history = resetNative ws := by
  induction ws generalizing start with
  | nil => rfl
  | cons w ws ih => simp [resetWireProgram, Straight.instantiate, resetNative, ih]

theorem resetNative_run (ws : List Wire) : (resetNative ws).run = (resetAll ws).run := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      simp only [resetNative, resetAll, measureResetWithCorrection, AdaptiveCircuit.run]
      rw [ih]
      rfl

theorem resetWireProgram_run {n : Nat} (ws : List Wire) (start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((resetWireProgram ws start).instantiate read history).run = (resetAll ws).run := by
  rw [resetWireProgram_instantiate, resetNative_run]

theorem resetWireProgram_wellFormed {n : Nat} (ws : List Wire) (start : Nat) :
    (resetWireProgram (n := n) ws start).WellFormed := by
  induction ws generalizing start with
  | nil => trivial
  | cons w ws ih => simp [resetWireProgram, Straight.WellFormed, ih]

theorem resetWireProgram_gateSlots {n : Nat} (ws : List Wire) (start : Nat) :
    (resetWireProgram (n := n) ws start).gateSlots = 0 := by
  induction ws generalizing start with
  | nil => rfl
  | cons w ws ih => simp [resetWireProgram, Straight.gateSlots, ih]

theorem fixedReset_records : fixedResetWires.length = 206624 := by
  simp [fixedResetWires, bitcoinQubitCount]

theorem fixedResetWireProgram_run {n start : Nat}
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    ((resetWireProgram fixedResetWires start).instantiate read history).run =
      (resetAll fixedResetWires).run := resetWireProgram_run _ _ _ _

theorem repeatFixed_history_length (a : AdaptiveCircuit) (width : Nat)
    (hLen : ∀ b ∈ a.run, b.history.length = width) (n : Nat)
    (b : InstrumentBranch) (hb : b ∈ (repeatFixed a n).run) : b.history.length = n * width := by
  induction n generalizing b with
  | zero => simp [repeatFixed, AdaptiveCircuit.run] at hb; subst b; simp
  | succ n ih =>
      rw [repeatFixed, AdaptiveCircuit.run_seq] at hb
      obtain ⟨first, hf, hb⟩ := List.mem_flatMap.mp hb
      obtain ⟨rest, hr, rfl⟩ := List.mem_map.mp hb
      simp [InstrumentBranch.seq, hLen first hf, ih rest hr, Nat.succ_mul, Nat.add_comm]

theorem fixedRepeated_history_length (Q : Point) (b : InstrumentBranch)
    (hb : b ∈ (fixedRepeated Q).run) : b.history.length = 5385536 := by
  exact repeatFixed_history_length _ _ (fixedResetTrial_length Q) 26 b hb

/-- Every proposed output index lies in the fixed complete transcript. -/
theorem fixed_output_index_bound (trial : Fin 26) (bit : Fin 512) :
    trial.val * 207136 + bit.val < 5385536 := by
  have ht := trial.isLt
  have hb := bit.isLt
  omega

end
end ShorECDLP.NaiveChallenge
