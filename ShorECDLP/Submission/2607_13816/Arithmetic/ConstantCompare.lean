import ShorECDLP.Submission.«2607_13816».Arithmetic.GidneyCompare
namespace ShorECDLP.Paper2607_13816
open Classical
/-- Literal source less-than wrapper, including constant-threshold shortcuts. -/
def controlledGidneyCompareLT (input dirty : List Wire) (threshold : Nat)
    (q c r t f : Wire) : Quantum.AdaptiveCircuit :=
  if threshold=0 then .done
  else if 2^input.length≤threshold then .unitary [.CX q f] .done
  else .unitary [.CX q f] (controlledGidneyCompareGE input dirty threshold q c r t f)

theorem controlledGidneyCompareLT_wellFormed (input dirty : List Wire) (threshold : Nat)
    (q c r t f : Wire) (hd : input.length=dirty.length)
    (hnd : ([q,c,r,t,f]++input++dirty).Nodup) :
    (controlledGidneyCompareLT input dirty threshold q c r t f).WellFormed := by
  have hqf : q≠f := by intro h; subst q; simp at hnd
  have hx : CircuitWellFormed [.CX q f] := by
    intro g hg; simp only [List.mem_singleton] at hg; subst g; exact hqf
  unfold controlledGidneyCompareLT
  split
  · trivial
  split
  · exact ⟨hx,trivial⟩
  · exact ⟨hx,controlledGidneyCompareGE_wellFormed input dirty threshold q c r t f hd hnd⟩

theorem controlledGidneyCompareLT_branch_correct (input dirty : List Wire) (threshold : Nat)
    (q c r t f : Wire) (s : BasisState) (hd : input.length=dirty.length)
    (hnd : ([q,c,r,t,f]++input++dirty).Nodup)
    (hc : s c=false) (hr : s r=false) (ht : s t=false)
    (branch : Quantum.InstrumentBranch)
    (hb : branch ∈ (controlledGidneyCompareLT input dirty threshold q c r t f).run) :
    let m := if threshold=0 ∨ 2^input.length≤threshold then 0 else input.length
    branch.history.length=m ∧ branch.kraus (Quantum.ket s)=Quantum.registerXResetMagnitude m •
      Quantum.ket (upd s f (Bool.xor (s f) (s q && decide (boolWordToNat (wireValues input s)<threshold)))) := by
  have hqf : q≠f := by intro h; subst q; simp at hnd
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
    have hh := gidneyDoneBranch branch (by simpa only [controlledGidneyCompareLT,if_pos rfl] using hb)
    rw [hh.1,hh.2]
    have he : upd s f (Bool.xor (s f) (s q && decide (boolWordToNat (wireValues input s)<0)))=s := by
      funext w; by_cases hw : w=f <;> simp [upd,hw]
    rw [he]
    simp [Quantum.registerXResetMagnitude]
  by_cases hlarge : 2^input.length≤threshold
  · have hh0 : boolWordToNat (wireValues input s)<2^input.length := by
      simpa only [wireValues,List.length_map] using boolWordToNat_lt_pow_two (wireValues input s)
    have hlt : boolWordToNat (wireValues input s)<threshold := by omega
    obtain ⟨last,hl,hh,hsem⟩ := gidneyUnitaryBranch [.CX q f] .done branch
      (by simpa only [controlledGidneyCompareLT,if_neg hz,if_pos hlarge] using hb)
    have hd := gidneyDoneBranch last hl
    rw [hh,hd.1,hsem,hd.2,Quantum.run_ket_agrees_classical _ s (by simp)]
    simp [hlarge,hlt,Quantum.registerXResetMagnitude,run,applyGate,Bool.xor_comm]
  obtain ⟨last,hl,hh,hsem⟩ := gidneyUnitaryBranch [.CX q f] _ branch
    (by simpa only [controlledGidneyCompareLT,if_neg hz,if_neg hlarge] using hb)
  have hg := controlledGidneyCompareGE_branch_correct input dirty threshold q c r t f
    (run [.CX q f] s) hd hnd (by simpa [run,applyGate,upd,hcf] using hc)
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
      simp [upd,hqf,hlt,hn]
    · have hn : threshold≤boolWordToNat (wireValues input s) := by omega
      simp [upd,hqf,hlt,hn]
  · simp [upd,hw]

/-- Nontrivial constant comparisons have three Toffolis per input bit minus one. -/
theorem controlledGidneyCompareLT_metrics (a : Wire) (input dirty : List Wire) (threshold : Nat)
    (q c r t f : Wire) (hd : (a::input).length=dirty.length)
    (hp0 : 0<threshold) (hp : threshold<2^(a::input).length) :
    let program := controlledGidneyCompareLT (a::input) dirty threshold q c r t f
    gidneyToffoliCount program=3*(a::input).length-1 ∧
    program.tCount=7*(3*(a::input).length-1) ∧ program.measurementCount=(a::input).length ∧
    (∀ w, w ∈ program.wires ↔ w ∈ [q,c,r,t,f]++(a::input)++dirty) := by
  cases dirty with
  | nil => simp at hd
  | cons d ds =>
    have hz : threshold≠0 := by omega
    have hlarge : ¬2^(a::input).length≤threshold := by omega
    let bits := (List.range (a::input).length).map (Nat.testBit (2^(a::input).length-threshold))
    have hbits : bits.length=(a::input).length := by simp [bits]
    cases he : bits with
    | nil => simp [he] at hbits
    | cons k ks =>
      have hk : input.length=ks.length := by rw [he] at hbits; simp only [List.length_cons] at hbits; omega
      have hds : input.length=ds.length := by simpa only [List.length_cons,Nat.succ.injEq] using hd
      have hm := controlledGidneyCompareCarry_metrics a d q c r t f input ds k ks hk hds
      have hpdef : controlledGidneyCompareLT (a::input) (d::ds) threshold q c r t f =
          .unitary [.CX q f] (controlledGidneyCompareCarry (a::input) (d::ds) (k::ks) q c r t f) := by
        simp only [controlledGidneyCompareLT,if_neg hz,if_neg hlarge,controlledGidneyCompareGE]
        change Quantum.AdaptiveCircuit.unitary _ (controlledGidneyCompareCarry _ _ bits _ _ _ _ _)=_
        rw [he]
      dsimp only
      rw [hpdef]
      refine ⟨?_,?_,?_,?_⟩
      · change 0+gidneyToffoliCount (controlledGidneyCompareCarry _ _ _ _ _ _ _ _)=_
        rw [Nat.zero_add,hm.1,List.length_cons]; omega
      · change 0+(controlledGidneyCompareCarry _ _ _ _ _ _ _ _).tCount=_
        rw [Nat.zero_add,hm.2.1,List.length_cons]; omega
      · exact hm.2.2
      · intro w
        have hw := controlledGidneyCompareCarry_wires_of_ne_control a d q c r t f input ds k ks hk hds w
        by_cases hq : w=q
        · subst w
          simp [Quantum.AdaptiveCircuit.wires,circuitWires,gateWires]
        · simp only [Quantum.AdaptiveCircuit.wires,circuitWires,List.flatMap_cons,List.flatMap_nil,
            gateWires,List.append_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
          rw [hw hq]
          simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
          tauto
end ShorECDLP.Paper2607_13816
