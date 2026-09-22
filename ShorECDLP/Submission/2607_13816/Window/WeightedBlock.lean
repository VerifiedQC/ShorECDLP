import ShorECDLP.Submission.«2607_13816».Window.RawBankReuse
/-! Connect the previously proved complete point-add block to the concrete bank exchange.
The full ordered arithmetic and Fourier histories are retained. -/
namespace ShorECDLP.Paper2607_13816
open Quantum
noncomputable section
theorem measuredWeightedBlock_relabel (P : ShorECDLP.Secp256k1.Point) (hP : P≠0)
    (hr : order • P=0) (j k : Nat) (prior : List Bool) :
    (measuredStreamBlock (streamPointCall P hP hr j) prior).relabel (streamBankPerm k)=
      ((AdaptiveCircuit.unitary ((List.range' (windowBankStart k) 16).map Gate.H) .done).seq
        (preparedWindowCall (fun _ => oddWindowX P j) (fun _ => oddWindowY P j)
          (fun _ => oddWindowTable_valid P hP hr j) k)).seq
        (semiclassicalFourier .inverse (List.range' (windowBankStart k) 16).reverse prior) := by
  simp only [measuredStreamBlock,AdaptiveCircuit.relabel_seq,streamPointCall_reuse,
    semiclassicalFourier_relabel,List.map_reverse,streamBankPerm_full,AdaptiveCircuit.relabel]
  have hh : (streamAddress.map Gate.H).map (Gate.relabel (streamBankPerm k))=
      (List.range' (windowBankStart k) 16).map Gate.H := by
    rw [←streamBankPerm_full k,List.map_map,List.map_map]
    rfl
  rw [hh]
theorem measuredWeightedBlock_run (P : ShorECDLP.Secp256k1.Point) (hP : P≠0)
    (hr : order • P=0) (j k : Nat) (hk : k≠0) (prior : List Bool)
    (ψ : State)
    (hin : SupportedOn (Clean (streamAddress++List.range' (windowBankStart k) 16)) ψ) :
    ((((AdaptiveCircuit.unitary ((List.range' (windowBankStart k) 16).map Gate.H) .done).seq
        (preparedWindowCall (fun _ => oddWindowX P j) (fun _ => oddWindowY P j)
          (fun _ => oddWindowTable_valid P hP hr j) k)).seq
        (semiclassicalFourier .inverse (List.range' (windowBankStart k) 16).reverse prior)).run.map
          (fun b => (b.history,b.kraus ψ)))=
      ((measuredStreamBlock (streamPointCall P hP hr j) prior).run.map
        (fun b => (b.history,b.kraus ψ))) := by
  rw [←measuredWeightedBlock_relabel P hP hr j k prior]
  apply measuredStreamBlock_relabel_run _ prior k hk _ ψ hin
  intro w hw
  have hs := streamPointCall_support P hP hr j hw
  simpa only [streamAllocation,List.mem_append,List.mem_range] using hs
end
end ShorECDLP.Paper2607_13816
