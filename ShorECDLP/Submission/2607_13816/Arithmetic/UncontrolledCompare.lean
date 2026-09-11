import ShorECDLP.Submission.«2607_13816».Arithmetic.GidneyCompare

/-!
# Uncontrolled measured constant comparison

Specialize the external control out of the verified Gidney comparator. The
fresh label below is only a compiler parameter; it occurs in no emitted gate
or measurement and consumes no physical qubit.
-/
namespace ShorECDLP.Paper2607_13816
open Classical
set_option linter.unusedSimpArgs false

private def gidneyCompareVirtualControl (input dirty : List Wire) (c r t f : Wire) : Wire :=
  ([c,r,t,f] ++ input ++ dirty).sum + 1

private theorem gidneyCompareVirtualControl_fresh (input dirty : List Wire) (c r t f : Wire) :
    gidneyCompareVirtualControl input dirty c r t f ∉ [c,r,t,f] ++ input ++ dirty := by
  intro h
  have hh : ([c,r,t,f] ++ input ++ dirty).sum + 1 ≤ ([c,r,t,f] ++ input ++ dirty).sum :=
    List.le_sum_of_mem h
  exact (Nat.not_succ_le_self _) hh

/-- Literal uncontrolled constant GE comparison, with no external control wire. -/
def gidneyCompareGE (input dirty : List Wire) (threshold : Nat) (carry spare ancilla flag : Wire) :
    Quantum.AdaptiveCircuit :=
  let q := gidneyCompareVirtualControl input dirty carry spare ancilla flag
  constantControlProgram q (controlledGidneyCompareGE input dirty threshold q carry spare ancilla flag)


/-- Every nontrivial unsigned GE threshold uses `3n - 1` Toffolis, with no
allocated external control. This count is independent of the threshold bits. -/
theorem gidneyCompareGE_toffoli_exact (a : Wire) (input dirty : List Wire) (p : Nat)
    (c r t f : Wire) (hd : (a :: input).length = dirty.length)
    (hp0 : 0 < p) (hp : p < 2 ^ (a :: input).length) :
    gidneyToffoliCount (gidneyCompareGE (a :: input) dirty p c r t f) =
      3 * (a :: input).length - 1 := by
  cases dirty with
  | nil => simp at hd
  | cons d ds =>
    let q := gidneyCompareVirtualControl (a :: input) (d :: ds) c r t f
    change gidneyToffoliCount (constantControlProgram q
      (controlledGidneyCompareGE (a :: input) (d :: ds) p q c r t f)) = _
    rw [gidneyToffoliCount_constantControl,controlledGidneyCompareGE,
      if_neg (by omega : p ≠ 0),if_neg (by omega : ¬ 2 ^ (a :: input).length ≤ p)]
    generalize he : (List.range (a :: input).length).map (Nat.testBit (2 ^ (a :: input).length - p)) = bits
    have hl : bits.length = (a :: input).length := by rw [← he,List.length_map,List.length_range]
    cases bits with
    | nil => simp at hl
    | cons k ks =>
      have hm := controlledGidneyCompareCarry_metrics a d q c r t f input ds k ks
        (by simpa using hl.symm) (by simpa using hd)
      exact hm.1.trans (by simp only [List.length_cons]; omega)

/-- Counts and complete physical support of every nontrivial constant threshold,
including even thresholds used by EEA input centering. -/
theorem gidneyCompareGE_metrics (a : Wire) (input dirty : List Wire) (p : Nat)
    (c r t f : Wire) (hd : (a :: input).length = dirty.length)
    (hp0 : 0 < p) (hp : p < 2 ^ (a :: input).length) :
    let ac := gidneyCompareGE (a :: input) dirty p c r t f
    gidneyToffoliCount ac = 3 * (a :: input).length - 1 ∧
    gidneyCnotCount ac = 6 * (a :: input).length + 1 ∧
    ac.tCount = 7 * (3 * (a :: input).length - 1) ∧
    ac.measurementCount = (a :: input).length ∧
    (∀ w, w ∈ ac.wires ↔ w ∈ [c,r,t,f] ++ (a :: input) ++ dirty) := by
  cases dirty with
  | nil => simp at hd
  | cons d ds =>
    let q := gidneyCompareVirtualControl (a :: input) (d :: ds) c r t f
    have hq : q ∉ [c,r,t,f] ++ (a :: input) ++ d :: ds :=
      gidneyCompareVirtualControl_fresh _ _ _ _ _ _
    dsimp only
    unfold gidneyCompareGE
    dsimp only
    unfold controlledGidneyCompareGE
    rw [if_neg (by omega : p ≠ 0),if_neg (by omega : ¬ 2 ^ (a :: input).length ≤ p)]
    generalize he : (List.range (a :: input).length).map (Nat.testBit (2 ^ (a :: input).length - p)) = bits
    have hl : bits.length = (a :: input).length := by rw [← he,List.length_map,List.length_range]
    cases bits with
    | nil => simp at hl
    | cons k ks =>
      have hk : input.length = ks.length := by simpa using hl.symm
      have hds : input.length = ds.length := by simpa using hd
      have h := controlledGidneyCompareCarry_metrics a d q c r t f input ds k ks hk hds
      have hcx := controlledGidneyCompareCarry_uncontrolled_cnot a d q c r t f input ds k ks hk hds hq
      dsimp only at h
      refine ⟨?_,hcx,?_,?_,?_⟩
      · rw [gidneyToffoliCount_constantControl,h.1]
        simp only [List.length_cons]; omega
      · rw [constantControlProgram_tCount,h.2.1]
        congr 1
      · rw [constantControlProgram_measurements,h.2.2]
        rfl
      · intro w
        have hsafe := controlledGidneyCompareCarry_controlSafe (a :: input) (d :: ds) (k :: ks) q c r t f hq
        rw [constantControlProgram_wires q _ hsafe]
        by_cases hw : w = q
        · subst w
          simpa only [ne_eq,not_true_eq_false,and_false,false_iff] using hq
        · rw [controlledGidneyCompareCarry_wires_of_ne_control a d q c r t f input ds k ks hk hds w hw]
          rw [show [q,c,r,t,f] ++ (a :: input) ++ d :: ds =
            q :: ([c,r,t,f] ++ (a :: input) ++ d :: ds) from rfl,List.mem_cons]
          exact ⟨fun h => h.1.resolve_left hw,fun h => ⟨Or.inr h,hw⟩⟩

/-- Every branch toggles only the result flag; all borrowed and clean workspace
is restored and the amplitude is positive and independent of the input word. -/
theorem gidneyCompareGE_branch_correct (input dirty : List Wire) (threshold : Nat)
    (c r t f : Wire) (s : BasisState) (hd : input.length = dirty.length)
    (hnd : ([c,r,t,f] ++ input ++ dirty).Nodup)
    (hc : s c = false) (hr : s r = false) (ht : s t = false)
    (branch : Quantum.InstrumentBranch) (hb : branch ∈ (gidneyCompareGE input dirty threshold c r t f).run) :
    let m := if threshold = 0 ∨ 2 ^ input.length ≤ threshold then 0 else input.length
    branch.history.length = m ∧ branch.kraus (Quantum.ket s) = Quantum.registerXResetMagnitude m •
      Quantum.ket (upd s f (Bool.xor (s f) (decide (threshold ≤ boolWordToNat (wireValues input s))))) := by
  let q := gidneyCompareVirtualControl input dirty c r t f
  have hq : q ∉ [c,r,t,f] ++ input ++ dirty := gidneyCompareVirtualControl_fresh input dirty c r t f
  have hneq : ∀ w ∈ [c,r,t,f] ++ input ++ dirty, w ≠ q := by
    intro w hw he
    subst w
    exact hq hw
  have hqc := hneq c (by simp)
  have hqr := hneq r (by simp)
  have hqt := hneq t (by simp)
  have hqf := hneq f (by simp)
  have hqi : q ∉ input := by intro hi; exact hq (by simp [hi])
  have hndq : ([q,c,r,t,f] ++ input ++ dirty).Nodup := by
    change (q :: ([c,r,t,f] ++ input ++ dirty)).Nodup
    exact List.nodup_cons.mpr ⟨hq,hnd⟩
  obtain ⟨before,hbefore,hh,htransfer⟩ := constantControlProgram_branch q
    (controlledGidneyCompareGE input dirty threshold q c r t f)
    (controlledGidneyCompareGE_controlSafe input dirty threshold q c r t f hq) branch hb
  have hbits : wireValues input (upd s q true) = wireValues input s := by
    apply List.map_congr_left
    intro w hw
    have hn : w ≠ q := by intro he; subst w; exact hqi hw
    simp [upd,hn]
  have hold := controlledGidneyCompareGE_branch_correct input dirty threshold q c r t f
    (upd s q true) hd hndq (by simpa [upd,hqc] using hc)
    (by simpa [upd,hqr] using hr) (by simpa [upd,hqt] using ht) before hbefore
  dsimp only at hold ⊢
  refine ⟨hh ▸ hold.1,?_⟩
  let result := upd s f (Bool.xor (s f) (decide (threshold ≤ boolWordToNat (wireValues input s))))
  have hcomm (b : Bool) : upd (upd s q true) f b = upd (upd s f b) q true := by
    funext w
    by_cases hwq : w = q
    · subst w; simp [upd,Ne.symm hqf]
    · by_cases hwf : w = f
      · subst w; simp [upd,hqf]
      · simp [upd,hwq,hwf]
  have hres := htransfer s result (Quantum.registerXResetMagnitude
    (if threshold = 0 ∨ 2 ^ input.length ≤ threshold then 0 else input.length)) ?_
  · have he : upd result q (s q) = result := by
      funext w
      by_cases hwq : w = q
      · subst w; simp [result,upd,Ne.symm hqf]
      · simp [upd,hwq]
    simpa only [he] using hres
  · simpa only [hbits,show (upd s q true) f = s f by simp [upd,hqf],
      show (upd s q true) q = true by simp, Bool.true_and,hcomm] using hold.2

/-- Well-formedness supplies probability preservation for arbitrary quantum states. -/
theorem gidneyCompareGE_wellFormed (input dirty : List Wire) (threshold : Nat)
    (c r t f : Wire) (hd : input.length = dirty.length)
    (hnd : ([c,r,t,f] ++ input ++ dirty).Nodup) :
    (gidneyCompareGE input dirty threshold c r t f).WellFormed := by
  apply constantControlProgram_wellFormed
  apply controlledGidneyCompareGE_wellFormed _ _ _ _ _ _ _ _ hd
  change (gidneyCompareVirtualControl input dirty c r t f :: ([c,r,t,f] ++ input ++ dirty)).Nodup
  exact List.nodup_cons.mpr ⟨gidneyCompareVirtualControl_fresh input dirty c r t f,hnd⟩

/-- Production uncontrolled comparison against the secp256k1 modulus. -/
def secp256k1UncontrolledGidneyCompare : Quantum.AdaptiveCircuit :=
  gidneyCompareGE (List.range' 4 256) (List.range' 260 256)
    (2 ^ 256 - (2 ^ 32 + 977)) 0 1 2 3

private def uncontrolledProductionQ : Wire :=
  gidneyCompareVirtualControl (List.range' 4 256) (List.range' 260 256) 0 1 2 3

set_option maxRecDepth 10000 in
private theorem uncontrolledProduction_core : secp256k1UncontrolledGidneyCompare =
    constantControlProgram uncontrolledProductionQ
      (controlledGidneyCompareCarry (List.range' 4 256) (List.range' 260 256)
        secp256k1ReductionConstantBits uncontrolledProductionQ 0 1 2 3) := by
  unfold secp256k1UncontrolledGidneyCompare gidneyCompareGE
  dsimp only
  unfold controlledGidneyCompareGE
  rw [if_neg (by decide)]
  simp only [List.length_range']
  rw [if_neg (by decide),Nat.sub_sub_self (by decide : 2 ^ 32 + 977 ≤ 2 ^ 256)]
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem uncontrolledProduction_layout :
    ([0,1,2,3] ++ List.range' 4 256 ++ List.range' 260 256).Nodup := by
  simp only [List.nodup_append]
  refine ⟨⟨by decide,List.nodup_range',?_⟩,List.nodup_range',?_⟩
  all_goals
    intro a ha b hb he
    simp at ha hb
    omega

private theorem uncontrolledProduction_fresh :
    uncontrolledProductionQ ∉ [0,1,2,3] ++ List.range' 4 256 ++ List.range' 260 256 :=
  gidneyCompareVirtualControl_fresh _ _ _ _ _ _

set_option maxRecDepth 100000 in
private theorem uncontrolledProduction_metrics :
    gidneyToffoliCount secp256k1UncontrolledGidneyCompare = 767 ∧
    secp256k1UncontrolledGidneyCompare.tCount = 5369 ∧
    secp256k1UncontrolledGidneyCompare.measurementCount = 256 := by
  have h := controlledGidneyCompareCarry_metrics 4 260 uncontrolledProductionQ 0 1 2 3
    (List.range' 5 255) (List.range' 261 255) true
    ((List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977))) (by simp) (by simp)
  rw [uncontrolledProduction_core,gidneyToffoliCount_constantControl,
    constantControlProgram_tCount,constantControlProgram_measurements,
    show List.range' 4 256 = 4 :: List.range' 5 255 from rfl,
    show List.range' 260 256 = 260 :: List.range' 261 255 from rfl,
    show secp256k1ReductionConstantBits = true ::
      (List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977)) from rfl]
  simpa only [List.length_range'] using h

set_option maxRecDepth 100000 in
private theorem uncontrolledProduction_cnot : gidneyCnotCount secp256k1UncontrolledGidneyCompare = 1537 := by
  rw [uncontrolledProduction_core,
    show List.range' 4 256 = 4 :: List.range' 5 255 from rfl,
    show List.range' 260 256 = 260 :: List.range' 261 255 from rfl,
    show secp256k1ReductionConstantBits = true ::
      (List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977)) from rfl]
  exact controlledGidneyCompareCarry_uncontrolled_cnot 4 260 uncontrolledProductionQ 0 1 2 3
    (List.range' 5 255) (List.range' 261 255) true
    ((List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977)))
    (by simp) (by simp) uncontrolledProduction_fresh

set_option maxRecDepth 100000 in
private theorem uncontrolledProduction_qubits : secp256k1UncontrolledGidneyCompare.qubitCount = 516 := by
  rw [uncontrolledProduction_core,
    show List.range' 4 256 = 4 :: List.range' 5 255 from rfl,
    show List.range' 260 256 = 260 :: List.range' 261 255 from rfl,
    show secp256k1ReductionConstantBits = true ::
      (List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977)) from rfl]
  exact controlledGidneyCompareCarry_uncontrolled_qubits 4 260 uncontrolledProductionQ 0 1 2 3
    (List.range' 5 255) (List.range' 261 255)
    ((List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977)))
    (by simp) (by simp) uncontrolledProduction_fresh uncontrolledProduction_layout

set_option maxRecDepth 100000 in
/-- Same-circuit correctness and exact production resources: the arbitrary flag
is XORed with `input ≥ p`, every other wire is restored, total probability is one,
and the circuit uses 767 CCX, 1,537 CX, 5,369 T, 256 resets and 516 physical wires. -/
theorem secp256k1UncontrolledGidneyCompare_correct_resources (s : BasisState)
    (hc : s 0 = false) (hr : s 1 = false) (ht : s 2 = false) :
    (∀ branch ∈ secp256k1UncontrolledGidneyCompare.run,
      branch.history.length = 256 ∧
      branch.kraus (Quantum.ket s) = Quantum.registerXResetMagnitude 256 •
        Quantum.ket (upd s 3 (Bool.xor (s 3) (decide
          (2 ^ 256 - (2 ^ 32 + 977) ≤ boolWordToNat (wireValues (List.range' 4 256) s)))))) ∧
    Quantum.Instrument.bornMass secp256k1UncontrolledGidneyCompare.run (Quantum.ket s) = 1 ∧
    secp256k1UncontrolledGidneyCompare.WellFormed ∧
    gidneyToffoliCount secp256k1UncontrolledGidneyCompare = 767 ∧
    gidneyCnotCount secp256k1UncontrolledGidneyCompare = 1537 ∧
    secp256k1UncontrolledGidneyCompare.tCount = 5369 ∧
    secp256k1UncontrolledGidneyCompare.measurementCount = 256 ∧
    secp256k1UncontrolledGidneyCompare.qubitCount = 516 := by
  have hd : (List.range' 4 256).length = (List.range' 260 256).length := by simp
  have hw := gidneyCompareGE_wellFormed _ _ (2 ^ 256 - (2 ^ 32 + 977)) 0 1 2 3 hd uncontrolledProduction_layout
  have hsmall : ¬ (2 ^ 256 - (2 ^ 32 + 977) = 0 ∨ 2 ^ 256 ≤ 2 ^ 256 - (2 ^ 32 + 977)) := by decide
  refine ⟨?_,?_,hw,uncontrolledProduction_metrics.1,uncontrolledProduction_cnot,
    uncontrolledProduction_metrics.2.1,uncontrolledProduction_metrics.2.2,uncontrolledProduction_qubits⟩
  · intro branch hb
    have h := gidneyCompareGE_branch_correct _ _ (2 ^ 256 - (2 ^ 32 + 977)) 0 1 2 3 s hd
      uncontrolledProduction_layout hc hr ht branch hb
    simpa only [List.length_range',if_neg hsmall] using h
  · exact Quantum.AdaptiveCircuit.run_bornMass_eq_one _ hw _ (Quantum.normSq_ket s)

end ShorECDLP.Paper2607_13816

namespace ShorECDLP.Paper2607_13816
/-- The actual uncontrolled nontrivial threshold comparator has an exact primitive vector. -/
theorem gidneyCompareGE_primitive_exact (a : Wire) (input dirty : List Wire) (p : Nat)
    (c r t f : Wire) (hd : (a::input).length=dirty.length)
    (hp0 : 0<p) (hp : p<2^(a::input).length) :
    let bits := (List.range (a::input).length).map (Nat.testBit (2^(a::input).length-p))
    primitiveResources (gidneyCompareGE (a::input) dirty p c r t f)=
      (⟨2*(input.length+1)+7*(bits.headD false).toNat+9*constantBitWeight bits.tail,
        4*(input.length+1),6*(input.length+1)+1,3*input.length+2,0,input.length+1⟩ : PrimitiveResources) := by
  cases dirty with
  | nil => simp at hd
  | cons d ds =>
    let q := gidneyCompareVirtualControl (a::input) (d::ds) c r t f
    have hq : q ∉ [c,r,t,f]++(a::input)++d::ds := gidneyCompareVirtualControl_fresh _ _ _ _ _ _
    dsimp only
    change primitiveResources (constantControlProgram q (controlledGidneyCompareGE (a::input) (d::ds) p q c r t f))=_
    rw [controlledGidneyCompareGE,if_neg (by omega : p≠0),if_neg (by omega : ¬2^(a::input).length≤p)]
    generalize he : (List.range (a::input).length).map (Nat.testBit (2^(a::input).length-p))=bits
    have hl : bits.length=(a::input).length := by rw [← he,List.length_map,List.length_range]
    cases bits with
    | nil => simp at hl
    | cons k ks =>
      exact controlledGidneyCompareCarry_lowered_primitive_exact a d q c r t f k input ds ks
        (by simpa using hl.symm) (by simpa using hd) hq
end ShorECDLP.Paper2607_13816
