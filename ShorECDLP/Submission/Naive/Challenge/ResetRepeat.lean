import ShorECDLP.Submission.Naive.Challenge.Readout
import ShorECDLP.Framework.Quantum.AdaptiveFrame
import ShorECDLP.Framework.Quantum.MeasurementUncompute
import ShorECDLP.Framework.Repetition

namespace ShorECDLP.NaiveChallenge
open Classical Quantum
noncomputable section

def resetAll (ws : List Wire) : AdaptiveCircuit :=
  measureResetWithCorrection ws (fun _ => [])

theorem resetAll_clean (ws : List Wire) (hn : ws.Nodup) (b : InstrumentBranch)
    (hb : b ∈ (resetAll ws).run) (ψ : State) :
    SupportedOn (Clean ws) (b.kraus ψ) := by
  rw [resetAll, run_measureResetWithCorrection] at hb
  obtain ⟨out, ho, rfl⟩ := List.mem_map.mp hb
  exact xResetRegisterKraus_clean ws out ψ (mem_boolTranscripts_length ho) hn

theorem resetAll_support (ws : List Wire) : (resetAll ws).wires ⊆ ws := by
  induction ws with
  | nil => exact List.Subset.refl _
  | cons w ws ih =>
      intro v hv
      simp only [resetAll, measureResetWithCorrection, AdaptiveCircuit.wires,
        List.mem_cons, List.mem_append] at hv
      rcases hv with rfl | hv | hv
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih hv)
      · exact List.mem_cons_of_mem _ (ih hv)

def resetTrial (program : AdaptiveCircuit) : AdaptiveCircuit :=
  program.seq (resetAll program.wires.dedup)

theorem wires_seq (a b : AdaptiveCircuit) (w : Wire) :
    w ∈ (a.seq b).wires ↔ w ∈ a.wires ∨ w ∈ b.wires := by
  induction a with
  | done => simp [AdaptiveCircuit.seq, AdaptiveCircuit.wires]
  | unitary c a ih => simp [AdaptiveCircuit.seq, AdaptiveCircuit.wires, ih, or_assoc]
  | xMeasureReset t a b ih1 ih2 =>
      simp only [AdaptiveCircuit.seq, AdaptiveCircuit.wires, List.mem_cons, List.mem_append, ih1, ih2]
      tauto

theorem resetTrial_support (program : AdaptiveCircuit) :
    (resetTrial program).wires ⊆ program.wires.dedup := by
  intro w hw
  rw [resetTrial, wires_seq] at hw
  rcases hw with hw | hw
  · simpa using hw
  · exact resetAll_support _ hw

theorem resetTrial_zero (program : AdaptiveCircuit) (b : InstrumentBranch)
    (hb : b ∈ (resetTrial program).run) :
    b.kraus (ket zeroBasisState) =
      (b.kraus (ket zeroBasisState)) zeroBasisState • ket zeroBasisState := by
  have hc : SupportedOn (Clean program.wires.dedup) (b.kraus (ket zeroBasisState)) := by
    rw [resetTrial, AdaptiveCircuit.run_seq] at hb
    obtain ⟨before, _, hb⟩ := List.mem_flatMap.mp hb
    obtain ⟨after, ha, rfl⟩ := List.mem_map.mp hb
    exact resetAll_clean _ (List.nodup_dedup _) after ha (before.kraus (ket zeroBasisState))
  have hs : SupportedOn (fun s => s = zeroBasisState) (b.kraus (ket zeroBasisState)) := by
    intro s hs
    funext w
    by_cases hw : w ∈ program.wires.dedup
    · exact hc s hs w hw
    · exact AdaptiveCircuit.branch_frame (resetTrial program) w false
        (fun h => hw (resetTrial_support program h)) b hb (ket zeroBasisState)
        (supportedOn_ket _ _ rfl) s hs
  ext s
  by_cases he : s = zeroBasisState
  · subst s; simp [ket]
  · have hz : (b.kraus (ket zeroBasisState)) s = 0 := by
      by_contra h
      exact he (hs s h)
    simp only [ket] at hz
    simp [ket, he, hz]
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

def repeatFixed (a : AdaptiveCircuit) : Nat → AdaptiveCircuit
  | 0 => .done
  | n+1 => a.seq (repeatFixed a n)
def repeatFailed (width : Nat) (accept : List Bool → Bool) : Nat → List Bool → Bool
  | 0, _ => true
  | n+1, hist => !accept (hist.take width) && repeatFailed width accept n (hist.drop width)
private theorem failed_seq (width : Nat) (accept : List Bool → Bool) (n : Nat)
    (b c : InstrumentBranch) (hb : b.history.length = width) :
    repeatFailed width accept (n+1) (b.seq c).history =
      (!accept b.history && repeatFailed width accept n c.history) := by
  simp [repeatFailed, InstrumentBranch.seq, ← hb]
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
theorem repeatFixedFailed_mass (a : AdaptiveCircuit) (width : Nat) (accept : List Bool → Bool)
    (hLen : ∀ b ∈ a.run, b.history.length = width)
    (hI : ∀ b∈a.run, b.kraus (ket zeroBasisState)=
      (b.kraus (ket zeroBasisState)) zeroBasisState • ket zeroBasisState) (n : Nat) :
    Instrument.bornMass ((repeatFixed a n).run.filter
      (fun b => repeatFailed width accept n b.history)) (ket zeroBasisState)=
      (Instrument.bornMass (a.run.filter (fun b => !accept b.history)) (ket zeroBasisState))^n := by
  induction n with
  | zero => simp [repeatFixed,repeatFailed,AdaptiveCircuit.run,Instrument.bornMass,normSq_ket]
  | succ n ih =>
    rw [repeatFixed,AdaptiveCircuit.run_seq]
    rw [filter_pair _ _ (fun b => !accept b.history)
      (fun b => repeatFailed width accept n b.history) _ (by
        intro b hb c _; exact failed_seq width accept n b c (hLen b hb))]
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
    Instrument.bornMass (repeatFixed a n).run (ket zeroBasisState)=1 := by
  induction n with
  | zero => simp [repeatFixed,AdaptiveCircuit.run,Instrument.bornMass,normSq_ket]
  | succ n ih => rw [repeatFixed,AdaptiveCircuit.run_seq,mass_seq_product _ _ hI,hM,ih,mul_one]
/-- Independent retry probability derived from actual sequential Kraus execution and reset. -/
theorem repeatFixedSuccess_mass (a : AdaptiveCircuit) (width : Nat) (accept : List Bool → Bool)
    (hLen : ∀ b ∈ a.run, b.history.length = width)
    (hI : ∀ b∈a.run, b.kraus (ket zeroBasisState)=
      (b.kraus (ket zeroBasisState)) zeroBasisState • ket zeroBasisState)
    (hM : Instrument.bornMass a.run (ket zeroBasisState)=1) (n : Nat) :
    Instrument.bornMass ((repeatFixed a n).run.filter
      (fun b => !repeatFailed width accept n b.history)) (ket zeroBasisState)=
      independentRetrySuccessProbability
        (Instrument.bornMass (a.run.filter (fun b => accept b.history)) (ket zeroBasisState)) n := by
  have hm := mass_complement a.run (fun b => accept b.history) (ket zeroBasisState)
  rw [hM] at hm
  have hf := repeatFixedFailed_mass a width accept hLen hI n
  have hc := mass_complement (repeatFixed a n).run
    (fun b => repeatFailed width accept n b.history) (ket zeroBasisState)
  rw [repeat_total a hI hM n,hf] at hc
  have he : Instrument.bornMass (a.run.filter (fun b => !accept b.history)) (ket zeroBasisState)=
      1-Instrument.bornMass (a.run.filter (fun b => accept b.history)) (ket zeroBasisState) := by linarith
  rw [he] at hc
  unfold independentRetrySuccessProbability
  linarith


theorem resetAll_wellFormed (ws : List Wire) : (resetAll ws).WellFormed := by
  induction ws with
  | nil => exact ⟨by simp [CircuitWellFormed], True.intro⟩
  | cons w ws ih => exact ⟨ih, ih⟩

theorem resetAll_mass (ws : List Wire) (ψ : State) :
    (resetAll ws).run.bornMass ψ = normSq ψ :=
  AdaptiveCircuit.run_preservesBornMass _ (resetAll_wellFormed ws) ψ

theorem resetAll_history_length (ws : List Wire) (b : InstrumentBranch)
    (hb : b ∈ (resetAll ws).run) : b.history.length = ws.length := by
  rw [resetAll, run_measureResetWithCorrection] at hb
  obtain ⟨out, ho, rfl⟩ := List.mem_map.mp hb
  exact mem_boolTranscripts_length ho

theorem resetTrial_history_length (a : AdaptiveCircuit) (width : Nat)
    (hLen : ∀ b ∈ a.run, b.history.length = width) (b : InstrumentBranch)
    (hb : b ∈ (resetTrial a).run) : b.history.length = width + a.wires.dedup.length := by
  rw [resetTrial, AdaptiveCircuit.run_seq] at hb
  obtain ⟨before, hbefore, hb⟩ := List.mem_flatMap.mp hb
  obtain ⟨after, hafter, rfl⟩ := List.mem_map.mp hb
  simp only [InstrumentBranch.seq, List.length_append,
    hLen before hbefore, resetAll_history_length _ after hafter]
theorem instrumentMass_seq_preserving (I J : Instrument) (ψ : State)
    (hJ : ∀ φ, Instrument.bornMass J φ=normSq φ) :
    Instrument.bornMass (Instrument.seq I J) ψ=Instrument.bornMass I ψ := by
  induction I with
  | nil => rfl
  | cons b I ih =>
    have he : Instrument.bornMass (J.map b.seq) ψ=normSq (b.kraus ψ) := by
      simpa only [Instrument.bornMass,List.map_map,InstrumentBranch.seq,LinearMap.comp_apply] using hJ (b.kraus ψ)
    simpa only [Instrument.seq,List.flatMap_cons,Instrument.bornMass,List.map_append,List.sum_append,
      List.map_cons,List.sum_cons] using congrArg₂ (·+·) he ih
theorem instrumentFilter_seq_first (I J : Instrument) (p z : InstrumentBranch → Bool)
    (hz : ∀ b∈I, ∀ a∈J, z (b.seq a)=p b) :
    (Instrument.seq I J).filter z=Instrument.seq (I.filter p) J := by
  induction I with
  | nil => rfl
  | cons b I ih =>
    have hm : (J.map b.seq).filter z=if p b then J.map b.seq else [] := by
      rw [List.filter_map]
      have he : J.filter (z ∘ b.seq)=J.filter (fun _ => p b) := by
        apply List.filter_congr
        intro a ha
        exact hz b (by simp) a ha
      rw [he]
      cases p b <;> simp
    have ht := ih (fun a ha c hc => hz a (by simp [ha]) c hc)
    unfold Instrument.seq at ht
    cases hp : p b <;> simp [Instrument.seq,List.filter_append,hm,hp,ht]

theorem resetTrial_total (a : AdaptiveCircuit)
    (hM : a.run.bornMass (ket zeroBasisState) = 1) :
    (resetTrial a).run.bornMass (ket zeroBasisState) = 1 := by
  rw [resetTrial, AdaptiveCircuit.run_seq,
    instrumentMass_seq_preserving _ _ _ (resetAll_mass _), hM]

theorem resetTrial_eventMass (a : AdaptiveCircuit) (width : Nat)
    (hLen : ∀ b ∈ a.run, b.history.length = width) (event : List Bool → Bool) (ψ : State) :
    Instrument.bornMass ((resetTrial a).run.filter
      (fun b => event (b.history.take width))) ψ =
    Instrument.bornMass (a.run.filter (fun b => event b.history)) ψ := by
  rw [resetTrial, AdaptiveCircuit.run_seq]
  rw [instrumentFilter_seq_first _ _ (fun b => event b.history) _ (by
    intro b hb c _
    simp [InstrumentBranch.seq, ← hLen b hb])]
  exact instrumentMass_seq_preserving _ _ _ (resetAll_mass _)

/-- Twenty-six actual sequential trials. Reset establishes independence; it is
not assumed as an external probability premise. Reset records are ignored. -/
theorem resetTrial_twentySix (a : AdaptiveCircuit) (width : Nat)
    (hLen : ∀ b ∈ a.run, b.history.length = width)
    (hM : a.run.bornMass (ket zeroBasisState) = 1) (event : List Bool → Bool) :
    Instrument.bornMass ((repeatFixed (resetTrial a) 26).run.filter
      (fun b => !repeatFailed (width + a.wires.dedup.length)
        (fun bits => event (bits.take width)) 26 b.history)) (ket zeroBasisState) =
      independentRetrySuccessProbability
        (Instrument.bornMass (a.run.filter (fun b => event b.history)) (ket zeroBasisState)) 26 := by
  rw [repeatFixedSuccess_mass _ _ _ (resetTrial_history_length a width hLen)
    (resetTrial_zero a) (resetTrial_total a hM)]
  rw [resetTrial_eventMass a width hLen]

end
end ShorECDLP.NaiveChallenge
