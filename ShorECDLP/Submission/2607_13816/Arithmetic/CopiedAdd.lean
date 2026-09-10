import ShorECDLP.Submission.«2607_13816».Arithmetic.HornerSupport

/-!
# Copied-control modular addition for Figure 14 squaring

The source square temporarily copies one addend bit into a distinct clean
control. Modular addition preserves that bit, so the final CX clears the copy.
This permits the multiplier and addend to be the same register without aliasing
the arithmetic primitive's control with its borrowed workspace.
-/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
/-- Copy one addend bit into the separate control, add, then restore that control. -/
def copiedModularAdd (input acc : List Wire) (correction : List Bool) (p : Nat)
    (bit q c r t f : Wire) : AdaptiveCircuit :=
  .unitary [.CX bit q] ((controlledModularAdd input acc correction p q c r t f).seq
    (.unitary [.CX bit q] .done))
def copiedModularAddIdealState (input acc : List Wire) (correction : List Bool) (p : Nat)
    (bit q c f : Wire) (s : BasisState) : BasisState :=
  Classical.run [.CX bit q] (modularAddIdealState input acc correction p q c f
    (Classical.run [.CX bit q] s))
private theorem copy_value (bit q w : Wire) (s : BasisState) :
    Classical.run [.CX bit q] s w = if w=q then Bool.xor (s q) (s bit) else s w := rfl
private theorem copy_frame (bit q : Wire) (s : BasisState) (ws : List Wire) (hq : q ∉ ws) :
    wireValues ws (Classical.run [.CX bit q] s) = wireValues ws s := by
  apply List.map_congr_left
  intro w hw
  rw [copy_value,if_neg (by intro h; subst w; exact hq hw)]
private theorem copy_geometry (input acc : List Wire) (bit q c r t f : Wire)
    (hb : bit ∈ input) (hnd : ([q,c,r,t,f]++input++acc).Nodup) :
    q ∉ input ∧ q ∉ acc ∧ bit ∉ acc ∧ bit ≠ q ∧ c ≠ q ∧ r ≠ q ∧ t ≠ q ∧ f ≠ q := by
  have hbase := (List.nodup_append.mp hnd)
  have haux := List.nodup_append.mp hbase.1
  have hqa : q ∈ [q,c,r,t,f]++input := by simp
  have hqi : q ∉ input := fun h => haux.2.2 q (by simp) q h rfl
  have hqacc : q ∉ acc := fun h => hbase.2.2 q hqa q h rfl
  have hbacc : bit ∉ acc := fun h => hbase.2.2 bit (by simp [hb]) bit h rfl
  have hn := haux.1
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn
  refine ⟨hqi,hqacc,hbacc,?_,?_,?_,?_,?_⟩
  · intro h; subst bit; exact hqi hb
  all_goals tauto

theorem copiedModularAddIdealState_correct (input acc : List Wire) (correction : List Bool) (p : Nat)
    (bit q c r t f : Wire) (s : BasisState) (hb : bit ∈ input)
    (hlen : input.length=acc.length) (hk : acc.length=correction.length)
    (hnd : ([q,c,r,t,f]++input++acc).Nodup) (hq : s q=false) (hc : s c=false) (hf : s f=false)
    (hp : p<2^acc.length) (hx : boolWordToNat (wireValues input s)<p)
    (hy : boolWordToNat (wireValues acc s)<p)
    (hconstant : boolWordToNat correction=2^acc.length-p) :
    boolWordToNat (wireValues acc (copiedModularAddIdealState input acc correction p bit q c f s)) =
      (boolWordToNat (wireValues acc s) + if s bit then boolWordToNat (wireValues input s) else 0)%p ∧
    ∀ w, w ∉ acc → copiedModularAddIdealState input acc correction p bit q c f s w=s w := by
  obtain ⟨hqi,hqa,hba,hbq,hcq,hrq,htq,hfq⟩ := copy_geometry input acc bit q c r t f hb hnd
  have hi := copy_frame bit q s input hqi
  have ha := copy_frame bit q s acc hqa
  have h := modularAddIdealState_correct input acc correction p q c r t f (Classical.run [.CX bit q] s)
    hlen hk hnd (by simpa only [copy_value,if_neg hcq] using hc)
    (by simpa only [copy_value,if_neg hfq] using hf) hp (by rw [hi]; exact hx) (by rw [ha]; exact hy) hconstant
  constructor
  · dsimp only [copiedModularAddIdealState]
    rw [copy_frame bit q _ acc hqa,h.1,hi,ha,copy_value,if_pos rfl,hq,Bool.false_xor]
  · intro w hw
    dsimp only [copiedModularAddIdealState]
    rw [copy_value]
    by_cases hwq : w=q
    · subst w
      rw [if_pos rfl,h.2 q hqa,h.2 bit hba,copy_value,copy_value,if_pos rfl,if_neg hbq]
      cases s q <;> cases s bit <;> rfl
    · rw [if_neg hwq,h.2 w hw,copy_value,if_neg hwq]
/-- Copying a source bit does not change measurement amplitudes or leave a copy behind. -/
theorem copiedModularAdd_branch_correct (input acc : List Wire) (correction : List Bool) (p : Nat)
    (bit q c r t f : Wire) (s : BasisState) (hbit : bit ∈ input)
    (hlen : input.length=acc.length) (hne : 0<acc.length) (hk : acc.length=correction.length)
    (hnd : ([q,c,r,t,f]++input++acc).Nodup)
    (hc : s c=false) (hr : s r=false) (ht : s t=false) (hf : s f=false)
    (hp : p<2^acc.length) (hx : boolWordToNat (wireValues input s)<p)
    (hy : boolWordToNat (wireValues acc s)<p)
    (hconstant : boolWordToNat correction=2^acc.length-p)
    (branch : InstrumentBranch) (hb : branch ∈ (copiedModularAdd input acc correction p bit q c r t f).run) :
    let m := acc.length + if correction.all (fun k => !k) then 0 else (input.take (acc.length-1)).length
    branch.history.length=m ∧ branch.kraus (ket s)=registerXResetMagnitude m •
      ket (copiedModularAddIdealState input acc correction p bit q c f s) := by
  obtain ⟨hqi,hqa,hba,hbq,hcq,hrq,htq,hfq⟩ := copy_geometry input acc bit q c r t f hbit hnd
  have hi := copy_frame bit q s input hqi
  have ha := copy_frame bit q s acc hqa
  obtain ⟨rest,hrest,hh,hkBranch⟩ := gidneyUnitaryBranch [.CX bit q] _ branch hb
  simp only [AdaptiveCircuit.run_seq,Instrument.seq,List.mem_flatMap,List.mem_map,
    AdaptiveCircuit.run_unitary_done,List.mem_singleton] at hrest
  obtain ⟨ab,hab,last,rfl,rfl⟩ := hrest
  have h := controlledModularAdd_branch_correct input acc correction p q c r t f
    (Classical.run [.CX bit q] s) hlen hne hk hnd
    (by simpa only [copy_value,if_neg hcq] using hc)
    (by simpa only [copy_value,if_neg hrq] using hr)
    (by simpa only [copy_value,if_neg htq] using ht)
    (by simpa only [copy_value,if_neg hfq] using hf)
    hp (by rw [hi]; exact hx) (by rw [ha]; exact hy) hconstant ab hab
  constructor
  · rw [hh]
    simpa only [InstrumentBranch.seq,List.length_append,List.length_nil,Nat.add_zero] using h.1
  · rw [hkBranch]
    simp only [InstrumentBranch.seq,LinearMap.comp_apply]
    rw [run_ket_agrees_classical _ _ (by simp [Classical.HPFree,Classical.IsClassicalGate]),h.2,map_smul,
      run_ket_agrees_classical _ _ (by simp [Classical.HPFree,Classical.IsClassicalGate])]
    rfl

theorem copiedModularAdd_wellFormed (input acc : List Wire) (correction : List Bool) (p : Nat)
    (bit q c r t f : Wire) (hb : bit ∈ input)
    (hlen : input.length=acc.length) (hne : 0<acc.length) (hk : acc.length=correction.length)
    (hnd : ([q,c,r,t,f]++input++acc).Nodup) :
    (copiedModularAdd input acc correction p bit q c r t f).WellFormed := by
  have hg := copy_geometry input acc bit q c r t f hb hnd
  have hcopy : CircuitWellFormed [.CX bit q] := by
    intro g h; simp only [List.mem_singleton] at h; subst g; exact hg.2.2.2.1
  exact ⟨hcopy,(controlledModularAdd_wellFormed _ _ _ _ _ _ _ _ _ hlen hne hk hnd).seq ⟨hcopy,trivial⟩⟩

/-- A single concrete square-accumulation step, controlled by bit zero of the addend. -/
def secp256k1CopiedModularAdd : AdaptiveCircuit :=
  .unitary [.CX 260 516] (secp256k1ModularAdd.seq (.unitary [.CX 260 516] .done))
private theorem copied_layout :
    ([516,1,2,3,0]++List.range' 260 256++List.range' 4 256).Nodup := by
  simp only [List.nodup_append]
  refine ⟨⟨by decide,List.nodup_range',?_⟩,List.nodup_range',?_⟩
  all_goals
    intro a ha b hb he
    simp at ha hb
    omega
private theorem copy_gateCount (cost : Gate → Nat) (p : AdaptiveCircuit) (bit q : Wire) :
    gidneyGateCount cost (.unitary [.CX bit q] (p.seq (.unitary [.CX bit q] .done))) =
    gidneyGateCount cost p + cost (.CX bit q) + cost (.CX bit q) := by
  change (cost (.CX bit q)+0)+gidneyGateCount cost (p.seq (.unitary [.CX bit q] .done))=_
  rw [modularGateCount_seq]
  change (cost (.CX bit q)+0)+(gidneyGateCount cost p+((cost (.CX bit q)+0)+0))=_
  omega
private theorem copy_tCount (p : AdaptiveCircuit) (bit q : Wire) :
    (AdaptiveCircuit.unitary [.CX bit q] (p.seq (.unitary [.CX bit q] .done))).tCount=p.tCount := by
  change 0+(p.seq (.unitary [.CX bit q] .done)).tCount=p.tCount
  have hseq (a b : AdaptiveCircuit) : (a.seq b).tCount=a.tCount+b.tCount := by
    induction a with
    | done => simp only [AdaptiveCircuit.seq,AdaptiveCircuit.tCount,Nat.zero_add]
    | unitary gates next ih => simpa only [AdaptiveCircuit.seq,AdaptiveCircuit.tCount,Nat.add_assoc] using congrArg (ShorECDLP.tCount gates + ·) ih
    | xMeasureReset w l r ihl ihr => simp only [AdaptiveCircuit.seq,AdaptiveCircuit.tCount,ihl,ihr,max_add_add_right]
  rw [hseq]
  change 0+(p.tCount+0)=p.tCount
  omega
private theorem copy_measurements (p : AdaptiveCircuit) (bit q : Wire) :
    (AdaptiveCircuit.unitary [.CX bit q] (p.seq (.unitary [.CX bit q] .done))).measurementCount=p.measurementCount := by
  change (p.seq (.unitary [.CX bit q] .done)).measurementCount=p.measurementCount
  rw [modularMeasurements_seq]
  change p.measurementCount+0=p.measurementCount
  omega
attribute [local irreducible] controlledModularAdd modularAddIdealState
  copiedModularAddIdealState wireValues boolWordToNat gidneyGateCount
private theorem copy_resources (program : AdaptiveCircuit) (bit q : Wire) :
    gidneyToffoliCount (.unitary [.CX bit q] (program.seq (.unitary [.CX bit q] .done))) = gidneyToffoliCount program ∧
    gidneyCnotCount (.unitary [.CX bit q] (program.seq (.unitary [.CX bit q] .done))) = gidneyCnotCount program + 2 ∧
    (AdaptiveCircuit.unitary [.CX bit q] (program.seq (.unitary [.CX bit q] .done))).tCount = program.tCount ∧
    (AdaptiveCircuit.unitary [.CX bit q] (program.seq (.unitary [.CX bit q] .done))).measurementCount = program.measurementCount := by
  constructor
  · unfold gidneyToffoliCount
    rw [copy_gateCount]
    simp only [Nat.add_zero]
  constructor
  · unfold gidneyCnotCount
    rw [copy_gateCount]
    simp only [Nat.add_assoc]
  exact ⟨copy_tCount program bit q,copy_measurements program bit q⟩
private theorem copied_resources :
    gidneyToffoliCount secp256k1CopiedModularAdd=2813 ∧
    gidneyCnotCount secp256k1CopiedModularAdd=4931 ∧
    secp256k1CopiedModularAdd.tCount=19691 ∧
    secp256k1CopiedModularAdd.measurementCount=511 := by
  have h := copy_resources secp256k1ModularAdd 260 516
  have hb := secp256k1ModularAdd_counts
  exact ⟨h.1.trans hb.1,h.2.1.trans (congrArg (· + 2) hb.2.1),
    h.2.2.1.trans hb.2.2.1,h.2.2.2.trans hb.2.2.2⟩
private theorem copied_support : secp256k1CopiedModularAdd.wires ⊆ List.range 517 := by
  have h := hornerMul256_wires_subset [516] (List.range' 260 256) (List.range' 4 256)
    secp256k1ReductionConstantBits.tail (2^256-(2^32+977)) 1 2 3 0
    List.length_range' List.length_range' (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have he : secp256k1ReductionConstantBits=true::secp256k1ReductionConstantBits.tail := by decide +kernel
  rw [← he] at h
  change secp256k1ModularAdd.wires ⊆ [1,2,3,0]++[516]++List.range' 260 256++List.range' 4 256 at h
  intro w hw
  change w ∈ (AdaptiveCircuit.unitary [.CX 260 516]
    (secp256k1ModularAdd.seq (.unitary [.CX 260 516] .done))).wires at hw
  simp only [AdaptiveCircuit.wires,modularWires_seq,circuitWires,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,gateWires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with hw | hw | hw
  · simp only [List.mem_range]; rcases hw with rfl | rfl <;> decide
  · have hh := h hw
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_range',List.mem_range] at hh ⊢
    dsimp only [Wire] at *; omega
  · simp only [List.mem_range]; rcases hw with rfl | rfl <;> decide
private theorem copied_qubits : secp256k1CopiedModularAdd.qubitCount ≤ 517 := by
  have hs : secp256k1CopiedModularAdd.wires.dedup.toFinset ⊆ (List.range 517).toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (copied_support (by simpa using hw))
  have hc := Finset.card_le_card hs
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _),
    List.toFinset_card_of_nodup (List.nodup_range (n := 517))] at hc
  simpa only [AdaptiveCircuit.qubitCount,List.length_range] using hc

/-- The square step's actual circuit restores its copied control and all other work.
Its two extra CX gates add no T gates, measurements, or new physical wires. -/
theorem secp256k1CopiedModularAdd_certificate (s : BasisState)
    (hq : s 516=false) (hc : s 1=false) (hr : s 2=false) (ht : s 3=false) (hf : s 0=false)
    (hx : boolWordToNat (wireValues (List.range' 260 256) s)<2^256-(2^32+977))
    (hy : boolWordToNat (wireValues (List.range' 4 256) s)<2^256-(2^32+977)) :
    let after := copiedModularAddIdealState (List.range' 260 256) (List.range' 4 256)
      secp256k1ReductionConstantBits (2^256-(2^32+977)) 260 516 1 0 s
    boolWordToNat (wireValues (List.range' 4 256) after) =
      (boolWordToNat (wireValues (List.range' 4 256) s) +
        if s 260 then boolWordToNat (wireValues (List.range' 260 256) s) else 0) % (2^256-(2^32+977)) ∧
    (∀ w, w ∉ List.range' 4 256 → after w=s w) ∧
    (∀ branch ∈ secp256k1CopiedModularAdd.run, branch.history.length=511 ∧
      branch.kraus (ket s)=registerXResetMagnitude 511 • ket after) ∧
    Instrument.bornMass secp256k1CopiedModularAdd.run (ket s)=1 ∧
    secp256k1CopiedModularAdd.WellFormed ∧
    gidneyToffoliCount secp256k1CopiedModularAdd=2813 ∧
    gidneyCnotCount secp256k1CopiedModularAdd=4931 ∧
    secp256k1CopiedModularAdd.tCount=19691 ∧
    secp256k1CopiedModularAdd.measurementCount=511 ∧
    secp256k1CopiedModularAdd.qubitCount ≤ 517 := by
  have hk : (List.range' 4 256).length=secp256k1ReductionConstantBits.length := by decide +kernel
  have hp : 2^256-(2^32+977)<2^256 := by decide +kernel
  have hv : boolWordToNat secp256k1ReductionConstantBits=
      2^256-(2^256-(2^32+977)) := by
    rw [secp256k1ReductionConstant_value]; decide +kernel
  have hbit : 260 ∈ List.range' 260 256 := by decide +kernel
  have hl : (List.range' 260 256).length=(List.range' 4 256).length := by simp only [List.length_range']
  have hn : 0<(List.range' 4 256).length := by decide +kernel
  have hs := copiedModularAddIdealState_correct (List.range' 260 256) (List.range' 4 256) secp256k1ReductionConstantBits (2^256-(2^32+977)) 260 516 1 2 3 0 s hbit hl hk copied_layout hq hc hf (by simpa only [List.length_range'] using hp) hx hy (by simpa only [List.length_range'] using hv)
  have hw := copiedModularAdd_wellFormed (List.range' 260 256) (List.range' 4 256) secp256k1ReductionConstantBits (2^256-(2^32+977)) 260 516 1 2 3 0 hbit hl hn hk copied_layout
  dsimp only
  refine ⟨hs.1,hs.2,?_,?_,hw,copied_resources.1,copied_resources.2.1,
    copied_resources.2.2.1,copied_resources.2.2.2,copied_qubits⟩
  · intro branch hb
    have h := copiedModularAdd_branch_correct (List.range' 260 256) (List.range' 4 256) secp256k1ReductionConstantBits (2^256-(2^32+977)) 260 516 1 2 3 0 s hbit hl hn hk copied_layout
      hc hr ht hf (by simpa only [List.length_range'] using hp) hx hy (by simpa only [List.length_range'] using hv) branch hb
    have hz : secp256k1ReductionConstantBits.all (fun k => !k)=false := by decide +kernel
    simpa only [List.length_range',List.length_take,hz,Bool.false_eq_true,if_false] using h
  · exact AdaptiveCircuit.run_bornMass_eq_one _ hw _ (normSq_ket s)

end ShorECDLP.Paper2607_13816
