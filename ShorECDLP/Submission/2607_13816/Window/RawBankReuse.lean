import ShorECDLP.Submission.«2607_13816».Fourier.Relabel
import ShorECDLP.Submission.«2607_13816».Window.WeightedBank
import ShorECDLP.Submission.«2607_13816».Window.StreamBlockClean
import ShorECDLP.Submission.«2607_13816».Window.RawSupport
/-! Exact raw window-bank relocation at a clean preparation/measurement boundary.
This does not reorder arithmetic with Fourier measurement or establish whole-trial
sampling equivalence. In particular it supplies no improved whole-trial space bound. -/
namespace ShorECDLP.Paper2607_13816
open Quantum
noncomputable section
theorem streamBankPerm_full (k : Nat) :
    streamAddress.map (streamBankPerm k)=List.range' (windowBankStart k) 16 := by
  apply List.ext_getElem
  · simp [streamAddress]
  · intro i hi hj
    simp only [List.getElem_map,streamAddress,List.getElem_range']
    simpa using streamBankPerm_address k i (by simpa [streamAddress] using hi)

/-- Relocate the raw arithmetic itself, without introducing the repaired core. -/
theorem parkedRawProgram_reuse (k : Nat) (x y : Nat → Nat) :
    (parkedRawProgram (fun _ => x) (fun _ => y) 0).relabel (streamBankPerm k)=
      parkedRawProgram (fun _ => x) (fun _ => y) k := by
  rw [parkedRawProgram,parkedRawProgram,AdaptiveCircuit.relabel_trans]
  apply AdaptiveCircuit.relabel_congr
  intro w hw
  exact streamBankPerm_address_comp k w (List.mem_range.mp (signedRawProgram_support x y hw))

theorem preparedRawProgram_reuse (k : Nat) (x y : Nat → Nat) :
    (preparedRawProgram (fun _ => x) (fun _ => y) 0).relabel (streamBankPerm k)=
      preparedRawProgram (fun _ => x) (fun _ => y) k := by
  simp only [preparedRawProgram,AdaptiveCircuit.relabel_seq,AdaptiveCircuit.relabel,
    windowPrepareCircuit_reuse]
  congr 2
  exact parkedRawProgram_reuse k x y

def measuredRawBankBlock (x y : Nat → Nat) (k : Nat) (prior : List Bool) : AdaptiveCircuit :=
  ((AdaptiveCircuit.unitary ((List.range' (windowBankStart k) 16).map Gate.H) .done).seq
    (preparedRawProgram (fun _ => x) (fun _ => y) k)).seq
      (semiclassicalFourier .inverse (List.range' (windowBankStart k) 16).reverse prior)

theorem measuredRawBankBlock_relabel (x y : Nat → Nat) (k : Nat) (prior : List Bool) :
    (measuredStreamBlock (preparedRawProgram (fun _ => x) (fun _ => y) 0) prior).relabel
      (streamBankPerm k)=measuredRawBankBlock x y k prior := by
  simp only [measuredStreamBlock,measuredRawBankBlock,AdaptiveCircuit.relabel_seq,
    preparedRawProgram_reuse,semiclassicalFourier_relabel,List.map_reverse,
    streamBankPerm_full,AdaptiveCircuit.relabel]
  have hh : (streamAddress.map Gate.H).map (Gate.relabel (streamBankPerm k))=
      (List.range' (windowBankStart k) 16).map Gate.H := by
    rw [←streamBankPerm_full k,List.map_map,List.map_map]
    rfl
  rw [hh]

/-- Exact ordered histories AND unnormalized states, including every raw arithmetic
measurement branch. Requires both banks clean at block entry, not good arithmetic inputs. -/
theorem measuredRawBankBlock_run (x y : Nat → Nat) (k : Nat) (hk : k≠0)
    (prior : List Bool) (ψ : State)
    (hin : SupportedOn (Clean (streamAddress++List.range' (windowBankStart k) 16)) ψ) :
    ((measuredRawBankBlock x y k prior).run.map (fun b => (b.history,b.kraus ψ)))=
      ((measuredStreamBlock (preparedRawProgram (fun _ => x) (fun _ => y) 0) prior).run.map
        (fun b => (b.history,b.kraus ψ))) := by
  rw [←measuredRawBankBlock_relabel x y k prior]
  apply measuredStreamBlock_relabel_run _ prior k hk _ ψ hin
  intro w hw
  have hs := preparedRawProgram_support (fun _ => x) (fun _ => y) 0 hw
  simpa only [List.mem_append,List.mem_range,windowBankStart,streamAddress,
    Nat.mul_zero,Nat.add_zero] using hs

/-- Consequently every history-based acceptance event has the same Born mass. -/
theorem measuredRawBankBlock_event (x y : Nat → Nat) (k : Nat) (hk : k≠0)
    (prior : List Bool) (ψ : State)
    (hin : SupportedOn (Clean (streamAddress++List.range' (windowBankStart k) 16)) ψ)
    (accept : List Bool → Bool) :
    (((measuredRawBankBlock x y k prior).run.filter (fun b => accept b.history)).map
      (fun b => normSq (b.kraus ψ))).sum =
    (((measuredStreamBlock (preparedRawProgram (fun _ => x) (fun _ => y) 0) prior).run.filter
      (fun b => accept b.history)).map (fun b => normSq (b.kraus ψ))).sum := by
  have h := congrArg (fun (xs : List (List Bool × State)) =>
    ((xs.filter (fun p => accept p.1)).map (fun p => normSq p.2)).sum)
    (measuredRawBankBlock_run x y k hk prior ψ hin)
  simpa only [List.filter_map,List.map_map,Function.comp_def] using h
end
end ShorECDLP.Paper2607_13816
