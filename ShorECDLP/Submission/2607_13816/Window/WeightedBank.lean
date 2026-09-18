import ShorECDLP.Framework.Quantum.RelabelCongr
import ShorECDLP.Submission.«2607_13816».Window.BankReusePerm
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section
theorem streamBankPerm_address_comp (k : Nat) (w : Wire) (hw : w<855) :
    streamBankPerm k (windowAddressPerm 855 (by omega) w)=
      windowAddressPerm (windowBankStart k) (by unfold windowBankStart; omega) w := by
  by_cases h : w<839
  · rw [windowAddressPerm_core _ _ _ h,streamBankPerm_core k w h,windowAddressPerm_core _ _ _ h]
  · have he : w=839+(w-839) := by dsimp only [Wire] at *; omega
    rw [he,windowAddressPerm_address _ _ _ (by dsimp only [Wire] at *; omega),
      streamBankPerm_address _ _ (by dsimp only [Wire] at *; omega),
      windowAddressPerm_address _ _ _ (by dsimp only [Wire] at *; omega)]
theorem parkedWindowProgram_reuse (k : Nat) (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a,ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a)) :
    (parkedWindowProgram 855 (by omega) x y hc).relabel (streamBankPerm k)=
      parkedWindowProgram (windowBankStart k) (by unfold windowBankStart; omega) x y hc := by
  rw [parkedWindowProgram,parkedWindowProgram,AdaptiveCircuit.relabel_trans]
  apply AdaptiveCircuit.relabel_congr
  intro w hw
  exact streamBankPerm_address_comp k w (List.mem_range.mp (signedLookupPointProgram_wires x y hc hw))
theorem streamBankPerm_bits (k : Nat) :
    (windowAddressBits 0).map (streamBankPerm k)=windowAddressBits k := by
  apply List.ext_getElem
  · simp [windowAddressBits]
  · intro i hi hj
    simp only [List.getElem_map,windowAddressBits,List.getElem_range']
    have hb : i<15 := by simpa [windowAddressBits] using hi
    simpa [windowBankStart] using streamBankPerm_address k i (by omega)
theorem windowPrepareCircuit_reuse (k : Nat) :
    (windowPrepareCircuit 0).map (Gate.relabel (streamBankPerm k))=windowPrepareCircuit k := by
  have hr := streamBankPerm_core k 836 (by decide)
  have hs := streamBankPerm_address k 15 (by decide)
  have hb := streamBankPerm_bits k
  simp only [windowPrepareCircuit,signedAddressCircuit,tableXorGates,List.map_append,List.map_map]
  change ((windowAddressBits 0).map (fun w => Gate.CX (streamBankPerm k 836) (streamBankPerm k w))) ++
      ((windowAddressBits 0).map (fun w => Gate.CX (streamBankPerm k (windowBankStart 0+15)) (streamBankPerm k w))) = _
  rw [hr]
  have hsign : streamBankPerm k (windowBankStart 0+15)=windowBankStart k+15 := by simpa [windowBankStart] using hs
  rw [hsign,←hb]
  simp only [List.map_map,Function.comp_def]
theorem preparedWindowCall_reuse (k : Nat) (x y : Nat → ShorECDLP.Fp)
    (hc : ∀ a,ShorECDLP.Secp256k1.curve.toAffine.Nonsingular (x a) (y a)) :
    (preparedWindowCall (fun _ => x) (fun _ => y) (fun _ => hc) 0).relabel (streamBankPerm k)=
      preparedWindowCall (fun _ => x) (fun _ => y) (fun _ => hc) k := by
  simp only [preparedWindowCall,AdaptiveCircuit.relabel_seq,AdaptiveCircuit.relabel,
    windowPrepareCircuit_reuse]
  congr 2
  exact parkedWindowProgram_reuse k x y hc
theorem streamPointCall_reuse (P : ShorECDLP.Secp256k1.Point) (hP : P≠0)
    (hr : order • P=0) (j k : Nat) :
    (streamPointCall P hP hr j).relabel (streamBankPerm k)=
      preparedWindowCall (fun _ => oddWindowX P j) (fun _ => oddWindowY P j)
        (fun _ => oddWindowTable_valid P hP hr j) k :=
  preparedWindowCall_reuse k _ _ _
end
end ShorECDLP.Paper2607_13816
