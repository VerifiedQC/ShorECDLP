import ShorECDLP.Submission.«2607_13816».Window.BankReusePerm
import ShorECDLP.Framework.Quantum.AdaptiveFrame
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section
attribute [local irreducible] AdaptiveCircuit.seq semiclassicalFourier
def measuredStreamBlock (call : AdaptiveCircuit) (prior : List Bool) : AdaptiveCircuit :=
  ((AdaptiveCircuit.unitary (streamAddress.map Gate.H) .done).seq call).seq
    (semiclassicalFourier .inverse streamAddress.reverse prior)
theorem measuredStreamBlock_clean (call : AdaptiveCircuit) (prior : List Bool)
    (b : InstrumentBranch) (hb : b∈(measuredStreamBlock call prior).run) (ψ : State) :
    SupportedOn (Clean streamAddress) (b.kraus ψ) := by
  rw [measuredStreamBlock,AdaptiveCircuit.run_seq] at hb
  obtain ⟨first,hfirst,hmap⟩ := List.mem_flatMap.mp hb
  obtain ⟨second,hsecond,rfl⟩ := List.mem_map.mp hmap
  rw [semiclassicalFourier_run] at hsecond
  obtain ⟨bs,hbs,rfl⟩ := List.mem_map.mp hsecond
  exact streamFourier_clean prior bs (first.kraus ψ)
theorem measuredStreamBlock_parked_clean (call : AdaptiveCircuit) (prior : List Bool)
    (k : Nat) (hk : k≠0)
    (hcall : ∀ w∈call.wires,w<839 ∨ w∈streamAddress)
    (b : InstrumentBranch) (hb : b∈(measuredStreamBlock call prior).run) (ψ : State)
    (hin : SupportedOn (Clean (List.range' (windowBankStart k) 16)) ψ) :
    SupportedOn (Clean (List.range' (windowBankStart k) 16)) (b.kraus ψ) := by
  intro s hs w hw
  apply (measuredStreamBlock call prior).branch_frame w false _ b hb ψ _ s hs
  · intro hm
    have hbnd : w∈(List.range 839++streamAddress) := by
      rw [measuredStreamBlock, modularWires_seq, modularWires_seq] at hm
      rcases hm with (hp | hp) | hp
      · simp only [AdaptiveCircuit.wires] at hp
        have hx : w∈streamAddress := by
          simpa [circuitWires,List.mem_flatMap,gateWires] using hp
        simp [hx]
      · rcases hcall w hp with h | h
        · simp [h]
        · simp [h]
      · rw [←fourierContinue_done] at hp
        exact fourierContinue_support .inverse streamAddress.reverse prior (fun _ => .done)
          (List.range 839++streamAddress)
          (by intro v hv; exact List.mem_append_right _ (List.mem_reverse.mp hv))
          (by intro h; simp [AdaptiveCircuit.wires]) hp
    simp only [List.mem_append,List.mem_range,List.mem_range'_1,streamAddress,windowBankStart] at hbnd hw
    dsimp only [Wire] at *
    omega
  · intro t ht
    exact hin t ht w hw
theorem measuredStreamBlock_relabel (call : AdaptiveCircuit) (prior : List Bool)
    (k : Nat) (hk : k≠0)
    (hcall : ∀ w∈call.wires,w<839 ∨ w∈streamAddress)
    (b : InstrumentBranch) (hb : b∈(measuredStreamBlock call prior).run) (ψ : State)
    (hin : SupportedOn (Clean (streamAddress++List.range' (windowBankStart k) 16)) ψ) :
    (b.relabel (streamBankPerm k)).kraus ψ=b.kraus ψ := by
  apply streamBankBranch_clean k b ψ hin
  intro s hs w hw
  rcases List.mem_append.mp hw with hw | hw
  · exact measuredStreamBlock_clean call prior b hb ψ s hs w hw
  · exact measuredStreamBlock_parked_clean call prior k hk hcall b hb ψ
      (by intro t ht v hv; exact hin t ht v (List.mem_append_right _ hv)) s hs w hw
theorem measuredStreamBlock_relabel_run (call : AdaptiveCircuit) (prior : List Bool)
    (k : Nat) (hk : k≠0)
    (hcall : ∀ w∈call.wires,w<839 ∨ w∈streamAddress)
    (ψ : State)
    (hin : SupportedOn (Clean (streamAddress++List.range' (windowBankStart k) 16)) ψ) :
    (((measuredStreamBlock call prior).relabel (streamBankPerm k)).run.map
      (fun b => (b.history,b.kraus ψ)))=
    ((measuredStreamBlock call prior).run.map (fun b => (b.history,b.kraus ψ))) := by
  rw [AdaptiveCircuit.run_relabel,List.map_map]
  apply List.map_congr_left
  intro b hb
  simp only [Function.comp_apply,InstrumentBranch.relabel]
  change (b.history,(b.relabel (streamBankPerm k)).kraus ψ)=(b.history,b.kraus ψ)
  rw [measuredStreamBlock_relabel call prior k hk hcall b hb ψ hin]
end
end ShorECDLP.Paper2607_13816
