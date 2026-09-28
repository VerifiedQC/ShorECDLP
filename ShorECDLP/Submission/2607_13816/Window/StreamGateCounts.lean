import ShorECDLP.Submission.«2607_13816».Window.StreamResetRepetition
/-! Gate counts for the actual streaming schedule, including all Fourier histories.
Phase gates use the repository cost model; no rotation synthesis is claimed. -/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
attribute [local irreducible] AdaptiveCircuit.seq physicalPointLookup preparedRawProgram
private theorem history_zero (cost : Gate → Nat)
    (hc : ∀ dir k w, cost (.P dir k w)=0) (dir : PhaseDir) (w : Wire) (bs : List Bool) (k : Nat) :
    ((fourierHistoryRotations dir w bs k).map cost).sum=0 := by
  induction bs generalizing k with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [fourierHistoryRotations,fourierFeedForward,hc,ih]
private theorem continue_zero (cost : Gate → Nat)
    (hc : ∀ dir k w, cost (.P dir k w)=0) (dir : PhaseDir) (ws : List Wire)
    (prior : List Bool) (next : List Bool → AdaptiveCircuit) (n : Nat)
    (hn : ∀ bs, gidneyGateCount cost (next bs)=n) :
    gidneyGateCount cost (fourierContinue dir ws prior next)=n := by
  induction ws generalizing prior with
  | nil => exact hn prior
  | cons w ws ih => simp [fourierContinue,gidneyGateCount,history_zero cost hc,ih]
private theorem axis_zero (cost : Gate → Nat)
    (hp : ∀ dir k w, cost (.P dir k w)=0) (hh : ∀ w, cost (.H w)=0)
    (calls : List AdaptiveCircuit) (prior : List Bool) (tail : AdaptiveCircuit) :
    gidneyGateCount cost (streamAxis calls prior tail)=
      (calls.map (gidneyGateCount cost)).sum+gidneyGateCount cost tail := by
  induction calls generalizing prior with
  | nil => simp [streamAxis]
  | cons c cs ih =>
    rw [streamAxis,modularGateCount_seq,modularGateCount_seq,
      continue_zero cost hp _ _ _ _ _ ih]
    simp [gidneyGateCount,List.map_map,Function.comp_def,hh,Nat.add_assoc]
private theorem history_phase (dir : PhaseDir) (w : Wire) (bs : List Bool) (k : Nat) :
    ((fourierHistoryRotations dir w bs k).map primitivePhaseCost).sum≤bs.length := by
  induction bs generalizing k with
  | nil => simp [fourierHistoryRotations]
  | cons b bs ih =>
    have h := ih (k+1)
    cases b <;> simp [fourierHistoryRotations,fourierFeedForward,primitivePhaseCost] <;> omega
private theorem continue_phase (dir : PhaseDir) (ws : List Wire) (prior : List Bool)
    (next : List Bool → AdaptiveCircuit) (n : Nat)
    (hn : ∀ bs, bs.length=ws.length+prior.length → gidneyGateCount primitivePhaseCost (next bs)≤n) :
    gidneyGateCount primitivePhaseCost (fourierContinue dir ws prior next)≤
      fourierPhaseCount ws.length prior.length+n := by
  induction ws generalizing prior with
  | nil => simpa [fourierContinue,fourierPhaseCount] using hn prior (by simp)
  | cons w ws ih =>
    have hf := ih (false::prior) (by intro bs hb; apply hn bs; simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hb)
    have ht := ih (true::prior) (by intro bs hb; apply hn bs; simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hb)
    have h := history_phase dir w prior 2
    simp only [fourierContinue,gidneyGateCount,List.length_cons,fourierPhaseCount] at *
    omega
private def axisPhaseBudget : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, p => fourierPhaseCount 16 p+axisPhaseBudget n (p+16)
private theorem axis_phase (calls : List AdaptiveCircuit) (prior : List Bool) (tail : AdaptiveCircuit) :
    gidneyGateCount primitivePhaseCost (streamAxis calls prior tail)≤
      (calls.map (gidneyGateCount primitivePhaseCost)).sum+
        axisPhaseBudget calls.length prior.length+gidneyGateCount primitivePhaseCost tail := by
  induction calls generalizing prior with
  | nil => simp [streamAxis,axisPhaseBudget]
  | cons c cs ih =>
    have hf := continue_phase .inverse streamAddress.reverse prior (fun bs => streamAxis cs bs tail)
      ((cs.map (gidneyGateCount primitivePhaseCost)).sum+axisPhaseBudget cs.length (prior.length+16)+gidneyGateCount primitivePhaseCost tail)
      (by intro bs hb; simp only [streamAddress,List.length_reverse,List.length_range',Nat.add_comm 16] at hb; simpa only [hb] using ih bs)
    rw [streamAxis,modularGateCount_seq,modularGateCount_seq]
    have hh : gidneyGateCount primitivePhaseCost (.unitary (streamAddress.map Gate.H) .done)=0 := by
      simp [gidneyGateCount,List.map_map,Function.comp_def,primitivePhaseCost]
    rw [hh]
    simp only [List.length_cons,List.map_cons,List.sum_cons,axisPhaseBudget] at *
    have hlen : streamAddress.reverse.length=16 := by simp [streamAddress]
    simp only [hlen] at hf
    omega

theorem streamRawTrial_toffoli (P Q : Point) :
    (primitiveResources (streamRawTrial P Q)).toffoli=2040822631 := by
  let cost : Gate → Nat := fun g => match g with | .CCX _ _ _ => 1 | _ => 0
  change gidneyGateCount cost (streamRawTrial P Q)=_
  have hc : ∀ R j, gidneyGateCount cost (streamRawCall R j)=72884182 := by
    intro R j
    exact (preparedRawProgram_counts _ _ 0).1
  have hl : ∀ table, gidneyGateCount cost (physicalPointLookup table)=65535 := by
    intro table
    change (primitiveResources (physicalPointLookup table)).toffoli=_
    rw [physicalPointLookup_primitive]; rfl
  rw [streamRawTrial,modularGateCount_seq,axis_zero cost (by intros; rfl) (by intros; rfl),
    axis_zero cost (by intros; rfl) (by intros; rfl)]
  simp only [streamRawLeftCalls,streamRawRightCalls,List.map_cons,List.map_map,List.sum_cons,
    Function.comp_def,hc,hl,gidneyGateCount,cost,Nat.add_zero,Nat.zero_add]
  norm_num

theorem streamRawTrial_phase_le (P Q : Point) :
    (primitiveResources (streamRawTrial P Q)).phase≤54168 := by
  have hc : ∀ R j, gidneyGateCount primitivePhaseCost (streamRawCall R j)=0 := by
    intro R j
    exact (preparedRawProgram_counts _ _ 0).2.1
  have hl : ∀ table, gidneyGateCount primitivePhaseCost (physicalPointLookup table)=0 := by
    intro table
    change (primitiveResources (physicalPointLookup table)).phase=_
    rw [physicalPointLookup_primitive]; rfl
  have hleft := axis_phase (streamRawLeftCalls P Q) List.nil
    (streamAxis (streamRawRightCalls Q) List.nil (.unitary [.X 836] .done))
  have hright := axis_phase (streamRawRightCalls Q) List.nil (.unitary [.X 836] .done)
  have hb : axisPhaseBudget 16 0=32640 ∧ axisPhaseBudget 13 0=21528 := by decide +kernel
  simp only [streamRawLeftCalls,streamRawRightCalls,List.map_cons,List.map_map,List.sum_cons,
    Function.comp_def,hc,hl,List.length_cons,List.length_map,List.length_reverse,List.length_range,
    List.length_nil,hb.1,hb.2] at hleft hright
  norm_num [gidneyGateCount,primitivePhaseCost] at hleft hright
  change gidneyGateCount primitivePhaseCost (streamRawTrial P Q)≤_
  rw [streamRawTrial,modularGateCount_seq]
  have hx : gidneyGateCount primitivePhaseCost (.unitary [.X 836] .done)=0 := rfl
  rw [hx]
  norm_num [streamRawLeftCalls,streamRawRightCalls]
  omega

theorem streamRawTrial_tCount_le (P Q : Point) : (streamRawTrial P Q).tCount≤14285812585 := by
  have h := primitiveResources_T_le (streamRawTrial P Q)
  rw [streamRawTrial_toffoli] at h
  have hp := streamRawTrial_phase_le P Q
  omega

attribute [local irreducible] streamRawTrial streamResetWires streamRepeatedProgram

private theorem repeat_counts (a : AdaptiveCircuit) (ws : List Wire) (n t p : Nat)
    (ht : (primitiveResources a).toffoli=t) (hp : (primitiveResources a).phase≤p) :
    (primitiveResources (repeatWindowProgram (a.seq (measureResetWithCorrection ws (fun _ => []))) n)).toffoli=n*t ∧
    (primitiveResources (repeatWindowProgram (a.seq (measureResetWithCorrection ws (fun _ => []))) n)).phase≤n*p := by
  rw [repeatWindowProgram_primitive,primitiveResources_seq,resetRegister_primitiveResources]
  simp only [scalePrimitives,PrimitiveResources.add,Nat.add_zero,ht]
  exact ⟨trivial,Nat.mul_le_mul_left n hp⟩
/-- Reset contributes no Toffoli or phase gates to the actual repeated program. -/
theorem streamRepeatedProgram_gate_counts (Q : Point) :
    (primitiveResources (streamRepeatedProgram Q)).toffoli=114286067336 ∧
    (primitiveResources (streamRepeatedProgram Q)).phase≤3033408 := by
  simpa only [streamRepeatedProgram,streamResetTrial,streamTrialReset] using
    repeat_counts (streamRawTrial G Q) (streamResetWires Q) 56 2040822631 54168
    (streamRawTrial_toffoli G Q) (streamRawTrial_phase_le G Q)

theorem streamRepeatedProgram_tCount_le (Q : Point) :
    (streamRepeatedProgram Q).tCount≤800005504760 := by
  have h := primitiveResources_T_le (streamRepeatedProgram Q)
  have hc := streamRepeatedProgram_gate_counts Q
  rw [hc.1] at h
  omega

/-- Gate bounds and success concern the same physical streaming reset-and-repeat program. -/
theorem streamRepeatedProgram_gate_certificate (Q : Point)
    (hG : G ≠ 0) (hQ : Q ≠ 0) (hrQ : order • Q=0) (d : Nat) (hd : Q=d • G) :
    (streamRepeatedProgram Q).qubitCount≤855 ∧
    (primitiveResources (streamRepeatedProgram Q)).toffoli=114286067336 ∧
    (streamRepeatedProgram Q).tCount≤800005504760 ∧
    (streamRepeatedProgram Q).measurementCount≤47471340560 ∧
    (99 : ℝ)/100 ≤ Instrument.bornMass ((streamRepeatedProgram Q).run.filter
      (fun b => (streamRepeatedCandidate Q b.history).isSome)) (ket zeroBasisState) ∧
    (∀ hist c, streamRepeatedCandidate Q hist=some c → c=(d : ZMod order)) :=
  ⟨streamRepeatedProgram_qubits Q,(streamRepeatedProgram_gate_counts Q).1,
    streamRepeatedProgram_tCount_le Q,streamRepeatedProgram_measurements Q,
    streamRepeatedCandidate_success Q hG hQ hrQ d hd,
    fun hist c hc => streamRepeatedCandidate_sound Q d hd hist c hc⟩
end
end ShorECDLP.Paper2607_13816
