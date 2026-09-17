import ShorECDLP.Submission.«2607_13816».Window.DirectPointLookup
namespace ShorECDLP.Paper2607_13816
open Classical Quantum ShorECDLP.Secp256k1
noncomputable section
private theorem input_valid (s : BasisState) (hs : PointInitializeValid s) :
    DirectPointLookupValid (List.range' 519 16) 836 s := by
  refine ⟨?_,?_,hs.1.2⟩
  · intro w hw
    apply hs.1.1.1 w
    simp only [List.mem_append,List.mem_range'_1] at hw ⊢
    omega
  · intro w hw
    have h : s w∈wireValues pointLogicalWires s := List.mem_map.mpr ⟨w,hw,rfl⟩
    rw [hs.2] at h
    exact (List.mem_replicate.mp h).2

private theorem raw_zero (s : BasisState) :
    tableAddressValue (List.range' 855 16) s=windowRawDigit 0 s := by
  simp [tableAddressValue,windowRawDigit,windowAddressBits,windowBankStart,
    List.range',wireValues,boolWordToNat]
  omega

def firstWindowTable (A P : Point) (i : Nat) : Point :=
  A+(signedWindowDigit 16 i • P+signedWindowHalfPoint P order)

private theorem first_state (A P : Point) (hP : P≠0) (hr : order • P=0)
    (s : BasisState) (hs : PointInitializeValid s) :
    preparedWindowCallState (fun k => oddWindowX P (k-0)) (fun k => oddWindowY P (k-0))
      (fun k => oddWindowTable_valid P hP hr (k-0)) 0 (pointWrite A s)=
    pointWrite (firstWindowTable A P (tableAddressValue (List.range' 855 16) s)) s := by
  have ha : tableAddressValue (List.range' 855 16) (pointWrite A s)=
      tableAddressValue (List.range' 855 16) s := by
    apply tableAddressValue_congr
    intro w hw
    apply pointWrite_frame
    simp only [List.mem_range'_1] at hw
    simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,
      List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1]
    dsimp only [Wire] at *
    omega
  rw [preparedOddWindowCallAt_correct P hP hr 0 0 A (pointWrite A s)
    (pointInitialize_ready A s hs).1 (pointWrite_coordinates A s),pointWrite_overwrite,
    ←raw_zero,ha]
  simp [firstWindowTable]

theorem firstWindowLookup_coherent (A P : Point) (hP : P≠0) (hr : order • P=0) :
    CoherentlyImplementsOn (physicalPointLookup (firstWindowTable A P))
      (Finsupp.lmapDomain ℂ ℂ (fun s =>
        preparedWindowCallState (fun k => oddWindowX P (k-0)) (fun k => oddWindowY P (k-0))
          (fun k => oddWindowTable_valid P hP hr (k-0)) 0 (pointWrite A s)))
      PointInitializeValid := by
  obtain ⟨cs,hcs,hcm⟩ := physicalPointLookup_coherent (firstWindowTable A P)
  have hc : CoherentlyImplementsOn (physicalPointLookup (firstWindowTable A P))
      (Finsupp.lmapDomain ℂ ℂ (fun s =>
        pointWrite (firstWindowTable A P (tableAddressValue (List.range' 855 16) s)) s))
      PointInitializeValid := ⟨cs,hcs.imp (fun b c hb s hs => hb s (input_valid s hs)),hcm⟩
  apply hc.congrIdeal
  intro s hs
  simpa [ket] using congrArg ket (first_state A P hP hr s hs).symm

end
end ShorECDLP.Paper2607_13816
