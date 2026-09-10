import ShorECDLP.Submission.«2607_13816».EEA.RemainderIteration
import ShorECDLP.Submission.«2607_13816».EEA.ScheduleLayout
namespace ShorECDLP.Paper2607_13816
open Classical
private theorem schedule_layout_at {r : IndexedStepRegisters} {n start count : Nat}
    (hl : IndexedScheduleLayout r n start count) (offset : Nat) (ho : offset<count) :
    IndexedStepLayout r n (start+offset) := by
  induction hl generalizing offset with
  | done => omega
  | @step start count head tail ih =>
    cases offset with
    | zero => simpa using head
    | succ k => simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using ih k (by omega)

/-- A reachable active boundary executes one Euclidean step on the fixed production allocation. -/
theorem secp256k1EEA_iteration_paperStep {x spent : Nat} {v : EEAState}
    (hx : 1≤x) (hxp : x<ShorECDLP.p)
    (hreach : PaperBoundaryReachable ShorECDLP.p x spent v) (hactive : v.rPrime≠0)
    (s : BasisState) (hpacked : IndexedPackedState indexedStepProductionRegisters 256 s v) :
    IndexedPackedState indexedStepProductionRegisters 256
      (run (indexedScheduleUnitary indexedStepProductionRegisters 256 (4*spent+1)
        (4*(paperQuotient v).size)) s) (paperStep v) := by
  let steps := (paperQuotient v).size
  have hclock := hreach.spent_add_remaining
  rw [paperQuotientWeight_nonterminal hactive] at hclock
  have hbound := secp256k1_paperMicrosteps_le_1620 hx hxp
  change 4*paperQuotientWeight (paperInitial ShorECDLP.p x)≤1620 at hbound
  have hwithin : 4*spent+4*steps≤1620 := by dsimp [steps]; omega
  have hl : ∀ offset<4*steps, IndexedStepLayout indexedStepProductionRegisters 256 (4*spent+1+offset) := by
    intro offset ho
    have h := schedule_layout_at secp256k1ScheduleLayout_production (4*spent+offset) (by
      change 4*spent+offset<1620
      omega)
    simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h
  have hresult := indexedScheduleUnitary_active_paperStep indexedStepProductionRegisters 256
    (4*spent+1) steps s v hpacked ShorECDLP.p x spent hreach
    ShorECDLP.Secp256k1.p_prime hx hxp (by norm_num [ShorECDLP.p]) (by norm_num [ShorECDLP.p])
    hactive rfl (by decide) (by decide) (by decide) rfl
    (fun offset ho => hl offset (by omega))
    (fun offset ho => by simpa only [Nat.add_assoc] using hl (steps+offset) (by omega))
    (fun offset ho => by simpa only [Nat.add_assoc] using hl (steps+steps+offset) (by omega))
    (by decide)
    (fun offset ho => by simpa only [Nat.add_assoc] using hl (steps+steps+steps+offset) (by omega))
  have hlen : steps+(steps+(steps+steps))=4*steps := by omega
  simpa only [hlen] using hresult
/-- The actual production schedule reaches the mathematical terminal state at its exact active clock. -/
theorem secp256k1EEA_active_paperRun {x spent : Nat} {v : EEAState}
    (hx : 1≤x) (hxp : x<ShorECDLP.p)
    (hreach : PaperBoundaryReachable ShorECDLP.p x spent v)
    (s : BasisState) (hpacked : IndexedPackedState indexedStepProductionRegisters 256 s v) :
    IndexedPackedState indexedStepProductionRegisters 256
      (run (indexedScheduleUnitary indexedStepProductionRegisters 256 (4*spent+1)
        (paperMicrosteps v)) s) (paperRun v) := by
  by_cases hterminal : v.rPrime=0
  · simpa only [paperMicrosteps,paperQuotientWeight_terminal hterminal,Nat.mul_zero,
      indexedScheduleUnitary,Classical.run_nil,paperRun_of_terminal hterminal] using hpacked
  · have hnext := secp256k1EEA_iteration_paperStep hx hxp hreach hterminal s hpacked
    have hi := secp256k1EEA_active_paperRun hx hxp
      (PaperBoundaryReachable.step hreach hterminal) _ hnext
    have hlen : paperMicrosteps v=4*(paperQuotient v).size+paperMicrosteps (paperStep v) := by
      simp only [paperMicrosteps,paperQuotientWeight_nonterminal hterminal,Nat.mul_add]
    rw [hlen,indexedScheduleUnitary_append,Classical.run_append,paperRun_of_nonterminal hterminal]
    have hstart : 4*spent+1+4*(paperQuotient v).size=4*(spent+(paperQuotient v).size)+1 := by omega
    rw [hstart]
    exact hi
termination_by v.rPrime
decreasing_by exact paperStep_rPrime_lt hterminal

/-- Reachability supplies adaptive cleanup for one production iteration. -/
theorem secp256k1EEA_iteration_adaptiveInput {x spent : Nat} {v : EEAState}
    (hx : 1≤x) (hxp : x<ShorECDLP.p)
    (hreach : PaperBoundaryReachable ShorECDLP.p x spent v) (hactive : v.rPrime≠0)
    (s : BasisState) (hpacked : IndexedPackedState indexedStepProductionRegisters 256 s v) :
    IndexedScheduleAdaptiveInput indexedStepProductionRegisters 256 (4*spent+1)
      (4*(paperQuotient v).size) s := by
  let steps := (paperQuotient v).size
  have hclock := hreach.spent_add_remaining
  rw [paperQuotientWeight_nonterminal hactive] at hclock
  have hbound := secp256k1_paperMicrosteps_le_1620 hx hxp
  change 4*paperQuotientWeight (paperInitial ShorECDLP.p x)≤1620 at hbound
  have hwithin : 4*spent+4*steps≤1620 := by dsimp [steps]; omega
  have hl : ∀ offset<4*steps, IndexedStepLayout indexedStepProductionRegisters 256 (4*spent+1+offset) := by
    intro offset ho
    have h := schedule_layout_at secp256k1ScheduleLayout_production (4*spent+offset) (by
      change 4*spent+offset<1620
      omega)
    simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h
  have hresult := indexedScheduleAdaptive_reachable_iteration_input indexedStepProductionRegisters 256
    (4*spent+1) steps s v hpacked ShorECDLP.p x spent hreach
    ShorECDLP.Secp256k1.p_prime hx hxp (by norm_num [ShorECDLP.p]) (by norm_num [ShorECDLP.p])
    hactive rfl (by decide) (by decide) (by decide) rfl
    (fun offset ho => hl offset (by omega))
    (fun offset ho => by simpa only [Nat.add_assoc] using hl (steps+offset) (by omega))
    (fun offset ho => by simpa only [Nat.add_assoc] using hl (steps+steps+offset) (by omega))
    (by decide)
    (fun offset ho => by simpa only [Nat.add_assoc] using hl (steps+steps+steps+offset) (by omega))
  have hlen : steps+(steps+(steps+steps))=4*steps := by omega
  simpa only [hlen] using hresult

/-- Every active production microstep satisfies the adaptive cleanup preconditions. -/
theorem secp256k1EEA_active_adaptiveInput {x spent : Nat} {v : EEAState}
    (hx : 1≤x) (hxp : x<ShorECDLP.p)
    (hreach : PaperBoundaryReachable ShorECDLP.p x spent v)
    (s : BasisState) (hpacked : IndexedPackedState indexedStepProductionRegisters 256 s v) :
    IndexedScheduleAdaptiveInput indexedStepProductionRegisters 256 (4*spent+1)
      (paperMicrosteps v) s := by
  by_cases hterminal : v.rPrime=0
  · simp only [paperMicrosteps,paperQuotientWeight_terminal hterminal,Nat.mul_zero,
      IndexedScheduleAdaptiveInput]
  · have hhead := secp256k1EEA_iteration_adaptiveInput hx hxp hreach hterminal s hpacked
    have hnext := secp256k1EEA_iteration_paperStep hx hxp hreach hterminal s hpacked
    have hi := secp256k1EEA_active_adaptiveInput hx hxp
      (PaperBoundaryReachable.step hreach hterminal) _ hnext
    have hlen : paperMicrosteps v=4*(paperQuotient v).size+paperMicrosteps (paperStep v) := by
      simp only [paperMicrosteps,paperQuotientWeight_nonterminal hterminal,Nat.mul_add]
    rw [hlen,indexedScheduleAdaptiveInput_append]
    refine ⟨hhead, ?_⟩
    have hstart : 4*spent+1+4*(paperQuotient v).size=4*(spent+(paperQuotient v).size)+1 := by omega
    rw [hstart]
    exact hi
termination_by v.rPrime
decreasing_by exact paperStep_rPrime_lt hterminal

end ShorECDLP.Paper2607_13816
