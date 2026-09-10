import ShorECDLP.Submission.«2607_13816».Arithmetic.UncontrolledCompare
namespace ShorECDLP.Paper2607_13816
open Classical
/-- Literal unconditional less-than comparison with source threshold shortcuts. -/
def gidneyCompareLT (input dirty : List Wire) (threshold : Nat) (c r t f : Wire) : Quantum.AdaptiveCircuit :=
  if threshold=0 then .done
  else if 2^input.length≤threshold then .unitary [.X f] .done
  else .unitary [.X f] (gidneyCompareGE input dirty threshold c r t f)

theorem gidneyCompareLT_wellFormed (input dirty : List Wire) (threshold : Nat) (c r t f : Wire)
    (hd : input.length=dirty.length) (hnd : ([c,r,t,f]++input++dirty).Nodup) :
    (gidneyCompareLT input dirty threshold c r t f).WellFormed := by
  unfold gidneyCompareLT
  split
  · trivial
  · split
    · simp [Quantum.AdaptiveCircuit.WellFormed,CircuitWellFormed,Gate.WellFormed]
    · exact ⟨by simp [CircuitWellFormed,Gate.WellFormed],gidneyCompareGE_wellFormed input dirty threshold c r t f hd hnd⟩
theorem gidneyCompareLT_branch_correct (input dirty : List Wire) (threshold : Nat)
    (c r t f : Wire) (s : BasisState) (hd : input.length=dirty.length)
    (hnd : ([c,r,t,f]++input++dirty).Nodup)
    (hc : s c=false) (hr : s r=false) (ht : s t=false)
    (branch : Quantum.InstrumentBranch)
    (hb : branch ∈ (gidneyCompareLT input dirty threshold c r t f).run) :
    let m := if threshold=0 ∨ 2^input.length≤threshold then 0 else input.length
    branch.history.length=m ∧ branch.kraus (Quantum.ket s)=Quantum.registerXResetMagnitude m •
      Quantum.ket (upd s f (Bool.xor (s f) (decide (boolWordToNat (wireValues input s)<threshold)))) := by
  have hcf : c≠f := by intro h; subst c; simp at hnd
  have hrf : r≠f := by intro h; subst r; simp at hnd
  have htf : t≠f := by intro h; subst t; simp at hnd
  have hfi : f ∉ input := by
    intro h
    have hh := (List.nodup_append.mp (List.nodup_append.mp hnd).1).2.2 f (by simp) f h rfl
    exact hh
  have hword (b : Bool) : wireValues input (upd s f b)=wireValues input s := by
    apply List.map_congr_left
    intro w hw
    have hn : w≠f := fun he => hfi (he ▸ hw)
    simp [upd,hn]
  dsimp only
  by_cases hz : threshold=0
  · subst threshold
    have hh := gidneyDoneBranch branch (by simpa only [gidneyCompareLT,if_pos rfl] using hb)
    rw [hh.1,hh.2]
    have he : upd s f (Bool.xor (s f) (decide (boolWordToNat (wireValues input s)<0)))=s := by
      funext w; by_cases hw : w=f <;> simp [upd,hw]
    rw [he]
    simp [Quantum.registerXResetMagnitude]
  by_cases hlarge : 2^input.length≤threshold
  · have hh0 : boolWordToNat (wireValues input s)<2^input.length := by
      simpa only [wireValues,List.length_map] using boolWordToNat_lt_pow_two (wireValues input s)
    have hlt : boolWordToNat (wireValues input s)<threshold := by omega
    obtain ⟨last,hl,hh,hsem⟩ := gidneyUnitaryBranch [.X f] .done branch
      (by simpa only [gidneyCompareLT,if_neg hz,if_pos hlarge] using hb)
    have hd := gidneyDoneBranch last hl
    rw [hh,hd.1,hsem,hd.2,Quantum.run_ket_agrees_classical _ s (by simp)]
    simp [hlarge,hlt,Quantum.registerXResetMagnitude,run,applyGate,Bool.xor_comm]
  obtain ⟨last,hl,hh,hsem⟩ := gidneyUnitaryBranch [.X f] _ branch
    (by simpa only [gidneyCompareLT,if_neg hz,if_neg hlarge] using hb)
  have hg := gidneyCompareGE_branch_correct input dirty threshold c r t f
    (run [.X f] s) hd hnd (by simpa [run,applyGate,upd,hcf] using hc)
    (by simpa [run,applyGate,upd,hrf] using hr) (by simpa [run,applyGate,upd,htf] using ht) last hl
  rw [hh,hsem,Quantum.run_ket_agrees_classical _ s (by simp)]
  refine ⟨hg.1,?_⟩
  rw [hg.2]
  congr 2
  simp only [run,List.foldl_cons,List.foldl_nil,applyGate]
  simp only [hword]
  funext w
  by_cases hw : w=f
  · subst w
    by_cases hlt : boolWordToNat (wireValues input s)<threshold
    · have hn : ¬threshold≤boolWordToNat (wireValues input s) := by omega
      simp [upd,hlt,hn]
    · have hn : threshold≤boolWordToNat (wireValues input s) := by omega
      simp [upd,hlt,hn]
  · simp [upd,hw]


end ShorECDLP.Paper2607_13816
