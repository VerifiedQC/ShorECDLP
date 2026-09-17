import ShorECDLP.Submission.«2607_13816».Window.Candidate
import ShorECDLP.Submission.«2607_13816».Window.ResetFrame
import ShorECDLP.Submission.«2607_13816».Window.Repetition
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
private theorem norm_smul (c : ℂ) (ψ : State) : normSq (c • ψ)=Complex.normSq c*normSq ψ := by
  unfold normSq
  rw [inner_smul_smul,←Complex.normSq_eq_conj_mul_self]
  simp
private theorem mass_smul (I : Instrument) (c : ℂ) (ψ : State) :
    Instrument.bornMass I (c • ψ)=Complex.normSq c*Instrument.bornMass I ψ := by
  unfold Instrument.bornMass
  simp only [map_smul,norm_smul]
  rw [List.sum_map_mul_left]
private theorem mass_seq_product (I J : Instrument)
    (hI : ∀ b∈I, b.kraus (ket zeroBasisState)=
      (b.kraus (ket zeroBasisState)) zeroBasisState • ket zeroBasisState) :
    Instrument.bornMass (Instrument.seq I J) (ket zeroBasisState)=
      Instrument.bornMass I (ket zeroBasisState)*Instrument.bornMass J (ket zeroBasisState) := by
  induction I with
  | nil => simp [Instrument.seq,Instrument.bornMass]
  | cons b I ih =>
    have hb := hI b (by simp)
    have ht := ih (fun c hc => hI c (by simp [hc]))
    have hm : Instrument.bornMass (J.map b.seq) (ket zeroBasisState)=
        normSq (b.kraus (ket zeroBasisState))*Instrument.bornMass J (ket zeroBasisState) := by
      calc
        _ = Instrument.bornMass J (b.kraus (ket zeroBasisState)) := by
          simp only [Instrument.bornMass,List.map_map]
          rfl
        _ = _ := by rw [hb,mass_smul,norm_smul,normSq_ket,mul_one]
    simp only [Instrument.seq,List.flatMap_cons,Instrument.bornMass,List.map_append,List.sum_append,
      List.map_cons,List.sum_cons,add_mul] at *
    exact congrArg₂ (·+·) hm ht

def repeatWindowProgram (a : AdaptiveCircuit) : Nat → AdaptiveCircuit
  | 0 => .done
  | n+1 => a.seq (repeatWindowProgram a n)
def repeatWindowFailed (a : AdaptiveCircuit) (accept : List Bool → Bool) : Nat → List Bool → Bool
  | 0, _ => true
  | n+1, hist => match consumeAdaptiveHistory a hist with
    | none => true
    | some rest => !accept (hist.take (hist.length-rest.length)) && repeatWindowFailed a accept n rest
private theorem failed_seq (a : AdaptiveCircuit) (accept : List Bool → Bool) (n : Nat)
    (b c : InstrumentBranch) (hb : b∈a.run) :
    repeatWindowFailed a accept (n+1) (b.seq c).history=
      (!accept b.history && repeatWindowFailed a accept n c.history) := by
  simp only [repeatWindowFailed,InstrumentBranch.seq,consumeAdaptiveHistory_run a b hb,
    List.length_append,Nat.add_sub_cancel_right,List.take_left]
private theorem filter_pair (I J : Instrument) (p q z : InstrumentBranch → Bool)
    (hz : ∀ b∈I, ∀ c∈J, z (b.seq c)=(p b && q c)) :
    (Instrument.seq I J).filter z=Instrument.seq (I.filter p) (J.filter q) := by
  induction I with
  | nil => rfl
  | cons b I ih =>
    have hm : (J.map b.seq).filter z=if p b then (J.filter q).map b.seq else [] := by
      rw [List.filter_map]
      have he : J.filter (z ∘ b.seq)=J.filter (fun c => p b && q c) := by
        apply List.filter_congr
        intro c hc
        exact hz b (by simp) c hc
      rw [he]
      cases p b <;> simp
    have ht := ih (fun b hb c hc => hz b (by simp [hb]) c hc)
    unfold Instrument.seq at ht
    cases hp : p b <;> simp [Instrument.seq,List.filter_append,hm,hp,ht]
theorem repeatWindowFailed_mass (a : AdaptiveCircuit) (accept : List Bool → Bool)
    (hI : ∀ b∈a.run, b.kraus (ket zeroBasisState)=
      (b.kraus (ket zeroBasisState)) zeroBasisState • ket zeroBasisState) (n : Nat) :
    Instrument.bornMass ((repeatWindowProgram a n).run.filter
      (fun b => repeatWindowFailed a accept n b.history)) (ket zeroBasisState)=
      (Instrument.bornMass (a.run.filter (fun b => !accept b.history)) (ket zeroBasisState))^n := by
  induction n with
  | zero => simp [repeatWindowProgram,repeatWindowFailed,AdaptiveCircuit.run,Instrument.bornMass,normSq_ket]
  | succ n ih =>
    rw [repeatWindowProgram,AdaptiveCircuit.run_seq]
    rw [filter_pair _ _ (fun b => !accept b.history)
      (fun b => repeatWindowFailed a accept n b.history) _ (by
        intro b hb c _; exact failed_seq a accept n b c hb)]
    rw [mass_seq_product _ _ (fun b hb => hI b (List.mem_filter.mp hb).1),ih,pow_succ]
    exact mul_comm _ _
private theorem mass_complement (I : Instrument) (p : InstrumentBranch → Bool) (ψ : State) :
    Instrument.bornMass (I.filter p) ψ+Instrument.bornMass (I.filter (fun b => !p b)) ψ=
      Instrument.bornMass I ψ := by
  induction I with
  | nil => simp [Instrument.bornMass]
  | cons b I ih => cases h : p b <;> simp [Instrument.bornMass,h] at * <;> linarith
private theorem repeat_total (a : AdaptiveCircuit)
    (hI : ∀ b∈a.run, b.kraus (ket zeroBasisState)=
      (b.kraus (ket zeroBasisState)) zeroBasisState • ket zeroBasisState)
    (hM : Instrument.bornMass a.run (ket zeroBasisState)=1) (n : Nat) :
    Instrument.bornMass (repeatWindowProgram a n).run (ket zeroBasisState)=1 := by
  induction n with
  | zero => simp [repeatWindowProgram,AdaptiveCircuit.run,Instrument.bornMass,normSq_ket]
  | succ n ih => rw [repeatWindowProgram,AdaptiveCircuit.run_seq,mass_seq_product _ _ hI,hM,ih,mul_one]
/-- Independent retry probability derived from actual sequential Kraus execution and reset. -/
theorem repeatWindowSuccess_mass (a : AdaptiveCircuit) (accept : List Bool → Bool)
    (hI : ∀ b∈a.run, b.kraus (ket zeroBasisState)=
      (b.kraus (ket zeroBasisState)) zeroBasisState • ket zeroBasisState)
    (hM : Instrument.bornMass a.run (ket zeroBasisState)=1) (n : Nat) :
    Instrument.bornMass ((repeatWindowProgram a n).run.filter
      (fun b => !repeatWindowFailed a accept n b.history)) (ket zeroBasisState)=
      independentRetrySuccessProbability
        (Instrument.bornMass (a.run.filter (fun b => accept b.history)) (ket zeroBasisState)) n := by
  have hm := mass_complement a.run (fun b => accept b.history) (ket zeroBasisState)
  rw [hM] at hm
  have hf := repeatWindowFailed_mass a accept hI n
  have hc := mass_complement (repeatWindowProgram a n).run
    (fun b => repeatWindowFailed a accept n b.history) (ket zeroBasisState)
  rw [repeat_total a hI hM n,hf] at hc
  have he : Instrument.bornMass (a.run.filter (fun b => !accept b.history)) (ket zeroBasisState)=
      1-Instrument.bornMass (a.run.filter (fun b => accept b.history)) (ket zeroBasisState) := by linarith
  rw [he] at hc
  unfold independentRetrySuccessProbability
  linarith

theorem repeatWindowProgram_resources (a : AdaptiveCircuit) (n : Nat) :
    (repeatWindowProgram a n).tCount=n*a.tCount ∧
    (repeatWindowProgram a n).measurementCount=n*a.measurementCount := by
  induction n with
  | zero => simp [repeatWindowProgram,AdaptiveCircuit.tCount,AdaptiveCircuit.measurementCount]
  | succ n ih =>
    have ht := modularGateCount_seq tCost a (repeatWindowProgram a n)
    simp only [gidneyGateCount_tCount,ih.1] at ht
    have hm := modularMeasurements_seq a (repeatWindowProgram a n)
    rw [ih.2] at hm
    exact ⟨(ht.trans (Nat.add_comm _ _)).trans (Nat.succ_mul n a.tCount).symm,
      (hm.trans (Nat.add_comm _ _)).trans (Nat.succ_mul n a.measurementCount).symm⟩
theorem repeatWindowProgram_support (a : AdaptiveCircuit) (n : Nat) :
    (repeatWindowProgram a n).wires ⊆ a.wires := by
  induction n with
  | zero => exact List.nil_subset _
  | succ n ih =>
    intro w hw
    rw [repeatWindowProgram,modularWires_seq] at hw
    exact hw.elim id (fun h => ih h)

/-- Return the first publicly verified candidate from the sequential trial histories. -/
def repeatWindowCandidate {α : Type} (a : AdaptiveCircuit) (decode : List Bool → Option α) :
    Nat → List Bool → Option α
  | 0, _ => none
  | n+1, hist => match consumeAdaptiveHistory a hist with
    | none => none
    | some rest => (decode (hist.take (hist.length-rest.length))).orElse
        (fun _ => repeatWindowCandidate a decode n rest)
theorem repeatWindowCandidate_failed {α : Type} (a : AdaptiveCircuit) (decode : List Bool → Option α)
    (n : Nat) (hist : List Bool) :
    (repeatWindowCandidate a decode n hist).isSome=
      !repeatWindowFailed a (fun h => (decode h).isSome) n hist := by
  induction n generalizing hist with
  | zero => rfl
  | succ n ih =>
    simp only [repeatWindowCandidate,repeatWindowFailed]
    cases h : consumeAdaptiveHistory a hist with
    | none => rfl
    | some rest =>
      cases hd : decode (hist.take (hist.length-rest.length)) <;> simp [ih]
theorem repeatWindowCandidate_sound {α : Type} (a : AdaptiveCircuit) (decode : List Bool → Option α)
    (c : α) (hd : ∀ hist v, decode hist=some v → v=c) (n : Nat) (hist : List Bool)
    (v : α) (hv : repeatWindowCandidate a decode n hist=some v) : v=c := by
  induction n generalizing hist with
  | zero => simp [repeatWindowCandidate] at hv
  | succ n ih =>
    simp only [repeatWindowCandidate] at hv
    cases hc : consumeAdaptiveHistory a hist with
    | none => simp [hc] at hv
    | some rest =>
      cases he : decode (hist.take (hist.length-rest.length)) with
      | none => exact ih rest (by simpa [hc,he] using hv)
      | some z =>
        have hz : z=v := by simpa [hc,he] using hv
        exact hz ▸ hd _ z he
theorem repeatWindowProgram_zero (a : AdaptiveCircuit)
    (ha : ∀ b∈a.run, b.kraus (ket zeroBasisState)=
      (b.kraus (ket zeroBasisState)) zeroBasisState • ket zeroBasisState)
    (n : Nat) (b : InstrumentBranch) (hb : b∈(repeatWindowProgram a n).run) :
    b.kraus (ket zeroBasisState)=
      (b.kraus (ket zeroBasisState)) zeroBasisState • ket zeroBasisState := by
  induction n generalizing b with
  | zero =>
    simp only [repeatWindowProgram,AdaptiveCircuit.run,List.mem_singleton] at hb
    subst b
    simp [ket]
  | succ n ih =>
    rw [repeatWindowProgram,AdaptiveCircuit.run_seq] at hb
    obtain ⟨first,hf,hb⟩ := List.mem_flatMap.mp hb
    obtain ⟨last,hl,he⟩ := List.mem_map.mp hb
    subst b
    have hfirst := ha first hf
    have hlast := ih last hl
    change last.kraus (first.kraus (ket zeroBasisState))=
      (last.kraus (first.kraus (ket zeroBasisState))) zeroBasisState • ket zeroBasisState
    rw [hfirst,map_smul,hlast]
    simp [ket]
/-- Twenty-six physical trials, each restoring the same allocated quantum wires. -/
def secpWindowRepeatedProgram (Q : Point) (hrQ : order • Q=0) : AdaptiveCircuit :=
  repeatWindowProgram (resetWindowTrial Q hrQ) 26
/-- A public decoder returns the first verified scalar, or none if all trials fail. -/
def secpWindowRepeatedCandidate (Q : Point) (hrQ : order • Q=0) (hist : List Bool) :
    Option (ZMod order) :=
  repeatWindowCandidate (resetWindowTrial Q hrQ) (resetWindowCandidate Q hrQ) 26 hist

theorem secpWindowRepeatedCandidate_sound (Q : Point) (hrQ : order • Q=0)
    (d : Nat) (hQd : Q=d • G) (hist : List Bool) (c : ZMod order)
    (hc : secpWindowRepeatedCandidate Q hrQ hist=some c) : c=(d:ZMod order) :=
  repeatWindowCandidate_sound _ _ (d:ZMod order) (resetWindowCandidate_sound Q hrQ d hQd) 26 hist c hc

theorem secpWindowRepeatedCandidate_mass (Q : Point) (hrQ : order • Q=0)
    (d : Nat) (hQd : Q=d • G) :
    Instrument.bornMass ((secpWindowRepeatedProgram Q hrQ).run.filter
      (fun b => (secpWindowRepeatedCandidate Q hrQ b.history).isSome)) (ket zeroBasisState)=
      independentRetrySuccessProbability (secpWindowSuccessMass Q hrQ d) 26 := by
  simp only [secpWindowRepeatedProgram,secpWindowRepeatedCandidate,repeatWindowCandidate_failed]
  rw [repeatWindowSuccess_mass _ _ (resetWindowTrial_zero_branch Q hrQ)
    (resetWindowTrial_total Q hrQ d hQd),resetWindowCandidate_mass Q hrQ d hQd]

theorem secpWindowRepeatedCandidate_success (Q : Point) (hrQ : order • Q=0)
    (d : Nat) (hQd : Q=d • G) :
    (99:ℝ)/100 ≤ Instrument.bornMass ((secpWindowRepeatedProgram Q hrQ).run.filter
      (fun b => (secpWindowRepeatedCandidate Q hrQ b.history).isSome)) (ket zeroBasisState) := by
  rw [secpWindowRepeatedCandidate_mass Q hrQ d hQd]
  exact secpWindowRetrySuccess Q hrQ d hQd

theorem secpWindowRepeatedProgram_clean (Q : Point) (hrQ : order • Q=0)
    (b : InstrumentBranch) (hb : b∈(secpWindowRepeatedProgram Q hrQ).run) :
    b.kraus (ket zeroBasisState)=
      (b.kraus (ket zeroBasisState)) zeroBasisState • ket zeroBasisState :=
  repeatWindowProgram_zero _ (resetWindowTrial_zero_branch Q hrQ) 26 b hb

theorem secpWindowRepeatedProgram_resources (Q : Point) (hrQ : order • Q=0) :
    (secpWindowRepeatedProgram Q hrQ).tCount=26*(secpWindowProgram Q hrQ).tCount ∧
    (secpWindowRepeatedProgram Q hrQ).measurementCount=
      26*((secpWindowProgram Q hrQ).measurementCount+1383) := by
  have h := repeatWindowProgram_resources (resetWindowTrial Q hrQ) 26
  rw [resetWindowTrial_resources Q hrQ |>.1,resetWindowTrial_resources Q hrQ |>.2] at h
  exact h

theorem secpWindowRepeatedProgram_qubitCount (Q : Point) (hrQ : order • Q=0) :
    (secpWindowRepeatedProgram Q hrQ).qubitCount≤1383 := by
  have hs : (secpWindowRepeatedProgram Q hrQ).wires.dedup.toFinset ⊆ windowResetWires.toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (resetWindowTrial_support Q hrQ
      (repeatWindowProgram_support _ 26 (by simpa using hw)))
  have hc := (Finset.card_le_card hs).trans (List.toFinset_card_le _)
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
  simpa only [AdaptiveCircuit.qubitCount,windowResetWires,List.length_append,List.length_range,List.length_range'] using hc
end
end ShorECDLP.Paper2607_13816
