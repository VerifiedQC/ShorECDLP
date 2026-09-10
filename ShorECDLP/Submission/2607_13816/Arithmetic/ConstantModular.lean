import ShorECDLP.Submission.«2607_13816».Arithmetic.ConstantCompare
import ShorECDLP.Submission.«2607_13816».Arithmetic.HornerMul
namespace ShorECDLP.Paper2607_13816
open Classical
private theorem constant_add_overflow (B p x y : Nat) (q : Bool)
    (hp : p<B) (hx : x<p) (hy : y<p) :
    (q && decide ((y+(if q then x else 0))%B<x))=decide (B≤y+(if q then x else 0)) := by
  cases q with
  | false => simp only [Bool.false_eq_true,if_false,Nat.add_zero,Bool.false_and]
             simp [show ¬B≤y by omega]
  | true =>
    simp only [if_true,Bool.true_and]
    by_cases hh : B≤y+x
    · have hb : y+x<2*B := by omega
      have hm : (y+x)%B=y+x-B := Nat.mod_eq_sub_mod hh |>.trans (Nat.mod_eq_of_lt (by omega))
      simp only [hm]
      simp [hh,show y+x-B<x by omega]
    · rw [Nat.mod_eq_of_lt (by omega)]
      simp [hh,show ¬y+x<x by omega]

/-- Source five-stage controlled addition of a canonical classical constant. -/
def controlledConstantModularAdd (target dirty : List Wire) (constant correction : List Bool)
    (p : Nat) (q c r t f : Wire) : Quantum.AdaptiveCircuit :=
  (controlledGidneyAddConst target (dirty.take (target.length-1)) constant q c r t).seq
    ((controlledGidneyCompareLT target dirty (boolWordToNat constant) q c r t f).seq
      ((gidneyCompareGE target dirty p c r t f).seq
        ((controlledGidneyAddConst target (dirty.take (target.length-1)) correction f c r t).seq
          (controlledGidneyCompareLT target dirty (boolWordToNat constant) q c r t f))))

def constantModularAddIdealState (target : List Wire) (constant correction : List Bool)
    (p : Nat) (q f : Wire) (s : BasisState) : BasisState :=
  let low := gidneyAddIdealState target constant q s
  let carried := upd low f (Bool.xor (low f) (low q && decide (boolWordToNat (wireValues target low)<boolWordToNat constant)))
  let flagged := upd carried f (Bool.xor (carried f) (decide (p≤boolWordToNat (wireValues target carried))))
  let mid := gidneyAddIdealState target correction f flagged
  upd mid f (Bool.xor (mid f) (mid q && decide (boolWordToNat (wireValues target mid)<boolWordToNat constant)))

private theorem word_upd_outside (target : List Wire) (s : BasisState) (f : Wire) (b : Bool)
    (hf : f ∉ target) : wireValues target (upd s f b)=wireValues target s := by
  apply List.map_congr_left
  intro w hw
  have hn : w≠f := fun he => hf (he ▸ hw)
  simp [upd,hn]

theorem constantModularAddIdealState_correct (target : List Wire) (constant correction : List Bool)
    (p : Nat) (q f : Wire) (s : BasisState)
    (hk : target.length=constant.length) (hr : target.length=correction.length)
    (hn : target.Nodup) (hq : q ∉ target) (hf : f ∉ target) (hqf : q≠f)
    (hclean : s f=false) (hp : p<2^target.length)
    (hx : boolWordToNat constant<p) (hy : boolWordToNat (wireValues target s)<p)
    (hcorrection : boolWordToNat correction=2^target.length-p) :
    boolWordToNat (wireValues target (constantModularAddIdealState target constant correction p q f s))=
      (boolWordToNat (wireValues target s)+(if s q then boolWordToNat constant else 0))%p ∧
    ∀ w, w ∉ target → constantModularAddIdealState target constant correction p q f s w=s w := by
  let low := gidneyAddIdealState target constant q s
  let carried := upd low f (Bool.xor (low f) (low q && decide (boolWordToNat (wireValues target low)<boolWordToNat constant)))
  let flagged := upd carried f (Bool.xor (carried f) (decide (p≤boolWordToNat (wireValues target carried))))
  let mid := gidneyAddIdealState target correction f flagged
  have hl := gidneyAddIdealState_correct target constant q s hk hn
  have hlq : low q=s q := hl.2 q hq
  have hlf : low f=false := (hl.2 f hf).trans hclean
  have hcw : wireValues target carried=wireValues target low := word_upd_outside target low f _ hf
  have hfw : wireValues target flagged=wireValues target low := (word_upd_outside target carried f _ hf).trans hcw
  let total := boolWordToNat (wireValues target s)+(if s q then boolWordToNat constant else 0)
  let flag := Bool.xor (decide (2^target.length≤total)) (decide (p≤total%2^target.length))
  have hflag : flagged f=flag := by
    simp only [flagged,upd_same,hcw]
    simp only [carried,upd_same]
    rw [hlf,hlq,hl.1]
    simp only [Bool.false_xor]
    rw [constant_add_overflow (2^target.length) p _ _ (s q) hp hx hy]
  have hm := gidneyAddIdealState_correct target correction f flagged hr hn
  have hmath := modularCorrection_correct (2^target.length) p (boolWordToNat constant)
    (boolWordToNat (wireValues target s)) (s q) hp hx hy
  have hmvalue : boolWordToNat (wireValues target mid)=total%p := by
    rw [hm.1,hfw,hl.1,hflag,hcorrection]
    exact hmath.1
  have hmflag : mid f=flag := (hm.2 f hf).trans hflag
  have hmq : mid q=s q := by
    calc
      mid q=flagged q := hm.2 q hq
      _=s q := by simp only [flagged,carried,upd,if_neg hqf,hlq]
  have hclear : Bool.xor (mid f) (mid q && decide (boolWordToNat (wireValues target mid)<boolWordToNat constant))=false := by
    rw [hmflag,hmq,hmvalue]
    have hh := hmath.2.2
    rw [hmath.1] at hh
    exact hh
  change boolWordToNat (wireValues target (upd mid f _))=_ ∧ ∀ w, w ∉ target → upd mid f _ w=s w
  rw [hclear]
  constructor
  · rw [word_upd_outside target mid f false hf,hmvalue]
  · intro w hw
    by_cases he : w=f
    · subst w
      simp only [upd_same,hclean]
    · have hh := hm.2 w hw
      have hlw := hl.2 w hw
      rw [upd_other _ _ _ he]
      calc
        mid w=flagged w := hh
        _=low w := by simp only [flagged,carried,upd,if_neg he]
        _=s w := hlw


theorem constantModular_layout (target dirty : List Wire) (q c r t f : Wire)
    (hnd : ([q,c,r,t,f]++target++dirty).Nodup) :
    ([q,c,r,t]++target++dirty.take (target.length-1)).Nodup ∧
    ([f,c,r,t]++target++dirty.take (target.length-1)).Nodup ∧
    ([c,r,t,f]++target++dirty).Nodup := by
  have hs : ([q,c,r,t,f]++dirty++target).Nodup := by
    simpa only [List.append_assoc] using
      ((List.perm_append_comm (l₁ := target) (l₂ := dirty)).append_left [q,c,r,t,f]).nodup_iff.mp
        (by simpa only [List.append_assoc] using hnd)
  refine ⟨?_,(modularAdd_layout dirty target q c r t f hs).2.2.1,(List.nodup_cons.mp hnd).2⟩
  exact hnd.sublist (List.Sublist.cons₂ q (List.Sublist.cons₂ c (List.Sublist.cons₂ r
    (List.Sublist.cons₂ t (List.Sublist.cons f ((List.Sublist.refl target).append
      (List.take_sublist (target.length-1) dirty)))))))

theorem controlledConstantModularAdd_wellFormed (target dirty : List Wire) (constant correction : List Bool)
    (p : Nat) (q c r t f : Wire) (hk : target.length=constant.length) (hr : target.length=correction.length)
    (hd : target.length=dirty.length) (hne : 0<target.length)
    (hnd : ([q,c,r,t,f]++target++dirty).Nodup) :
    (controlledConstantModularAdd target dirty constant correction p q c r t f).WellFormed := by
  have hl := constantModular_layout target dirty q c r t f hnd
  have ht : target.length=(dirty.take (target.length-1)).length+1 := by simp only [List.length_take]; omega
  exact (controlledGidneyAddConst_wellFormed target _ constant q c r t hk ht hl.1).seq
    ((controlledGidneyCompareLT_wellFormed target dirty _ q c r t f hd hnd).seq
      ((gidneyCompareGE_wellFormed target dirty p c r t f hd hl.2.2).seq
        ((controlledGidneyAddConst_wellFormed target _ correction f c r t hr ht hl.2.1).seq
          (controlledGidneyCompareLT_wellFormed target dirty _ q c r t f hd hnd))))

theorem controlledConstantModularAdd_branch_correct (target dirty : List Wire) (constant correction : List Bool)
    (p : Nat) (q c r t f : Wire) (s : BasisState)
    (hk : target.length=constant.length) (hr : target.length=correction.length)
    (hd : target.length=dirty.length) (hne : 0<target.length)
    (hnd : ([q,c,r,t,f]++target++dirty).Nodup)
    (hc : s c=false) (hr0 : s r=false) (ht0 : s t=false)
    (branch : Quantum.InstrumentBranch)
    (hb : branch ∈ (controlledConstantModularAdd target dirty constant correction p q c r t f).run) :
    branch.kraus (Quantum.ket s)=Quantum.registerXResetMagnitude branch.history.length •
      Quantum.ket (constantModularAddIdealState target constant correction p q f s) := by
  have hl := constantModular_layout target dirty q c r t f hnd
  have htake : target.length=(dirty.take (target.length-1)).length+1 := by simp only [List.length_take]; omega
  have hn := (List.nodup_append.mp (List.nodup_append.mp hnd).1).2.1
  have hnot (w : Wire) (hw : w ∈ [q,c,r,t,f]) : w ∉ target := by
    intro h; exact (List.nodup_append.mp (List.nodup_append.mp hnd).1).2.2 w hw w h rfl
  have hcf : c≠f := by intro h; subst c; simp at hnd
  have hrf : r≠f := by intro h; subst r; simp at hnd
  have htf : t≠f := by intro h; subst t; simp at hnd
  let low := gidneyAddIdealState target constant q s
  let carried := upd low f (Bool.xor (low f) (low q && decide (boolWordToNat (wireValues target low)<boolWordToNat constant)))
  let flagged := upd carried f (Bool.xor (carried f) (decide (p≤boolWordToNat (wireValues target carried))))
  let mid := gidneyAddIdealState target correction f flagged
  have hlow (w : Wire) (hw : w ∉ target) : low w=s w := (gidneyAddIdealState_correct target constant q s hk hn).2 w hw
  have hcarried (w : Wire) (hw : w ∉ target) (hf : w≠f) : carried w=s w := by
    simp only [carried,upd,if_neg hf,hlow w hw]
  have hflagged (w : Wire) (hw : w ∉ target) (hf : w≠f) : flagged w=s w := by
    simp only [flagged,upd,if_neg hf,hcarried w hw hf]
  have hmid (w : Wire) (hw : w ∉ target) (hf : w≠f) : mid w=s w :=
    ((gidneyAddIdealState_correct target correction f flagged hr hn).2 w hw).trans (hflagged w hw hf)
  apply horner_seq_branch _ _ s low _ ?_ ?_ branch hb
  · intro b hb
    have hh := controlledGidneyAddConst_branch_correct target _ constant q c r t s hk htake hl.1 hc hr0 ht0 b hb
    rw [hh.1]; exact hh.2
  · intro b hb
    apply horner_seq_branch _ _ low carried _ ?_ ?_ b hb
    · intro b hb
      have hh := controlledGidneyCompareLT_branch_correct target dirty _ q c r t f low hd hnd
        ((hlow c (hnot c (by simp))).trans hc) ((hlow r (hnot r (by simp))).trans hr0)
        ((hlow t (hnot t (by simp))).trans ht0) b hb
      rw [hh.1]; exact hh.2
    · intro b hb
      apply horner_seq_branch _ _ carried flagged _ ?_ ?_ b hb
      · intro b hb
        have hh := gidneyCompareGE_branch_correct target dirty p c r t f carried hd hl.2.2
          ((hcarried c (hnot c (by simp)) hcf).trans hc) ((hcarried r (hnot r (by simp)) hrf).trans hr0)
          ((hcarried t (hnot t (by simp)) htf).trans ht0) b hb
        rw [hh.1]; exact hh.2
      · intro b hb
        apply horner_seq_branch _ _ flagged mid _ ?_ ?_ b hb
        · intro b hb
          have hh := controlledGidneyAddConst_branch_correct target _ correction f c r t flagged hr htake hl.2.1
            ((hflagged c (hnot c (by simp)) hcf).trans hc) ((hflagged r (hnot r (by simp)) hrf).trans hr0)
            ((hflagged t (hnot t (by simp)) htf).trans ht0) b hb
          rw [hh.1]; exact hh.2
        · intro b hb
          have hh := controlledGidneyCompareLT_branch_correct target dirty _ q c r t f mid hd hnd
            ((hmid c (hnot c (by simp)) hcf).trans hc) ((hmid r (hnot r (by simp)) hrf).trans hr0)
            ((hmid t (hnot t (by simp)) htf).trans ht0) b hb
          rw [hh.1]; exact hh.2
private theorem constant_five_counts (a b c d : Quantum.AdaptiveCircuit) :
    gidneyToffoliCount (a.seq (b.seq (c.seq (d.seq b))))=
      gidneyToffoliCount a+(gidneyToffoliCount b+(gidneyToffoliCount c+(gidneyToffoliCount d+gidneyToffoliCount b))) ∧
    (a.seq (b.seq (c.seq (d.seq b)))).tCount=a.tCount+(b.tCount+(c.tCount+(d.tCount+b.tCount))) ∧
    (a.seq (b.seq (c.seq (d.seq b)))).measurementCount=
      a.measurementCount+(b.measurementCount+(c.measurementCount+(d.measurementCount+b.measurementCount))) := by
  have hcc (x y : Quantum.AdaptiveCircuit) : gidneyToffoliCount (x.seq y)=gidneyToffoliCount x+gidneyToffoliCount y := modularGateCount_seq _ x y
  have ht (x y : Quantum.AdaptiveCircuit) : (x.seq y).tCount=x.tCount+y.tCount := by
    simpa only [gidneyGateCount_tCount] using modularGateCount_seq tCost x y
  simp only [hcc,ht,modularMeasurements_seq,and_self]
private theorem increment_bits_value : boolWordToNat ((List.range 256).map (Nat.testBit 1))=1 := by
  exact gidneyCompareBits_value 256 1 (by decide +kernel)
/-- Controlled increment modulo secp256k1, using the literal five source stages. -/
def secp256k1ControlledIncrement : Quantum.AdaptiveCircuit :=
  controlledConstantModularAdd (List.range' 4 256) (List.range' 260 256)
    ((List.range 256).map (Nat.testBit 1)) secp256k1ReductionConstantBits
    (2^256-(2^32+977)) 516 1 2 3 0
attribute [local irreducible] controlledGidneyAddConst controlledGidneyCompareLT gidneyCompareGE
private theorem increment_decompose : secp256k1ControlledIncrement =
    (controlledGidneyAddConst (List.range' 4 256) (List.range' 260 255)
      ((List.range 256).map (Nat.testBit 1)) 516 1 2 3).seq
    ((controlledGidneyCompareLT (List.range' 4 256) (List.range' 260 256) 1 516 1 2 3 0).seq
      ((gidneyCompareGE (List.range' 4 256) (List.range' 260 256) (2^256-(2^32+977)) 1 2 3 0).seq
        ((controlledGidneyAddConst (List.range' 4 256) (List.range' 260 255) secp256k1ReductionConstantBits 0 1 2 3).seq
          (controlledGidneyCompareLT (List.range' 4 256) (List.range' 260 256) 1 516 1 2 3 0)))) := by
  unfold secp256k1ControlledIncrement controlledConstantModularAdd
  have ht : (List.range' 260 256).take 255 = List.range' 260 255 := by decide +kernel
  simp only [increment_bits_value, List.length_range', Nat.reduceSub, ht]
attribute [local irreducible] controlledConstantModularAdd constantModularAddIdealState wireValues boolWordToNat
private theorem increment_metrics :
    gidneyToffoliCount secp256k1ControlledIncrement=3829 ∧
    secp256k1ControlledIncrement.tCount=26803 ∧ secp256k1ControlledIncrement.measurementCount=1278 := by
  have ha := secp256k1Increment_counts 516 1 2 3
  have hb := controlledGidneyCompareLT_metrics 4 (List.range' 5 255) (List.range' 260 256) 1 516 1 2 3 0
    (by simp) (by decide) (by simp only [List.length_cons,List.length_range']; decide +kernel)
  have hs : 4 :: List.range' 5 255 = List.range' 4 256 := by decide +kernel
  simp only [hs, List.length_range'] at hb
  have hc := secp256k1ModularCompare_counts 1 2 3 0
  have hd := secp256k1GidneyAdd_counts 0 1 2 3
  have h := constant_five_counts
    (controlledGidneyAddConst (List.range' 4 256) (List.range' 260 255) ((List.range 256).map (Nat.testBit 1)) 516 1 2 3)
    (controlledGidneyCompareLT (List.range' 4 256) (List.range' 260 256) 1 516 1 2 3 0)
    (gidneyCompareGE (List.range' 4 256) (List.range' 260 256) (2^256-(2^32+977)) 1 2 3 0)
    (controlledGidneyAddConst (List.range' 4 256) (List.range' 260 255) secp256k1ReductionConstantBits 0 1 2 3)
  rw [increment_decompose]
  refine ⟨h.1.trans ?_,h.2.1.trans ?_,h.2.2.trans ?_⟩
  · rw [ha.1,hb.1,hc.1,hd.1]
  · rw [ha.2.2.1,hb.2.1,hc.2.2.1,hd.2.2.1]
  · rw [ha.2.2.2,hb.2.2.1,hc.2.2.2,hd.2.2.2]

private theorem oddConstant256_wires (bits : List Bool) (hk : bits.length=255) (q c r t w : Wire) :
    w ∈ (controlledGidneyAddConst (List.range' 4 256) (List.range' 260 255) (true::bits) q c r t).wires ↔
      w ∈ [q,c,r,t]++List.range' 4 256++List.range' 260 255 := by
  exact controlledGidneyAddConst_wires 4 260 q c r t (List.range' 5 255) (List.range' 261 254) bits
    (by simpa using hk.symm) (by simp) w
private theorem increment_qubits : secp256k1ControlledIncrement.qubitCount=517 := by
  have hbits : (List.range 256).map (Nat.testBit 1)=true::(List.range' 1 255).map (Nat.testBit 1) := by decide +kernel
  have hb := controlledGidneyCompareLT_metrics 4 (List.range' 5 255) (List.range' 260 256) 1 516 1 2 3 0
    (by simp) (by decide) (by simp only [List.length_cons,List.length_range']; decide +kernel)
  have hs : 4 :: List.range' 5 255 = List.range' 4 256 := by decide +kernel
  simp only [hs,List.length_range'] at hb
  have heq : secp256k1ControlledIncrement.wires.dedup.toFinset=(List.range 517).toFinset := by
    ext w
    simp only [List.mem_toFinset,List.mem_dedup,increment_decompose,modularWires_seq]
    rw [hbits,oddConstant256_wires _ (by simp),hb.2.2.2,secp256k1ModularCompare_wires,
      show secp256k1ReductionConstantBits=true::(List.range' 1 255).map (Nat.testBit (2^32+977)) from rfl,
      oddConstant256_wires _ (by simp)]
    simp
    dsimp only [Wire] at *
    omega
  have h := congrArg Finset.card heq
  simpa only [List.toFinset_card_of_nodup (List.nodup_dedup _),
    List.toFinset_card_of_nodup (List.nodup_range),List.length_range] using h
private theorem increment_layout : ([516,1,2,3,0]++List.range' 4 256++List.range' 260 256 : List Wire).Nodup := by
  simp only [List.nodup_append]
  refine ⟨⟨by decide,List.nodup_range',?_⟩,List.nodup_range',?_⟩
  all_goals
    intro a ha b hb he
    simp at ha hb
    dsimp only [Wire] at *
    omega

/-- The same five-stage circuit conditionally increments a canonical field value,
restores every other wire, and has normalized branch mass and exact resources. -/
theorem secp256k1ControlledIncrement_correct_resources (s : BasisState)
    (hc : s 1=false) (hr : s 2=false) (ht : s 3=false) (hf : s 0=false)
    (hy : boolWordToNat (wireValues (List.range' 4 256) s)<2^256-(2^32+977)) :
    let out := constantModularAddIdealState (List.range' 4 256) ((List.range 256).map (Nat.testBit 1))
      secp256k1ReductionConstantBits (2^256-(2^32+977)) 516 0 s
    boolWordToNat (wireValues (List.range' 4 256) out)=
      (boolWordToNat (wireValues (List.range' 4 256) s)+(if s 516 then 1 else 0))%(2^256-(2^32+977)) ∧
    (∀ w, w ∉ List.range' 4 256 → out w=s w) ∧
    (∀ b ∈ secp256k1ControlledIncrement.run,
      b.kraus (Quantum.ket s)=Quantum.registerXResetMagnitude b.history.length • Quantum.ket out) ∧
    (∀ ψ, Quantum.Instrument.bornMass secp256k1ControlledIncrement.run ψ=Quantum.normSq ψ) ∧
    secp256k1ControlledIncrement.WellFormed ∧
    gidneyToffoliCount secp256k1ControlledIncrement=3829 ∧
    secp256k1ControlledIncrement.tCount=26803 ∧
    secp256k1ControlledIncrement.measurementCount=1278 ∧
    secp256k1ControlledIncrement.qubitCount=517 := by
  have hk : (List.range' 4 256).length=((List.range 256).map (Nat.testBit 1)).length := by simp
  have hv : (List.range' 4 256).length=secp256k1ReductionConstantBits.length := by simp [secp256k1ReductionConstantBits]
  have hw : secp256k1ControlledIncrement.WellFormed := controlledConstantModularAdd_wellFormed
    _ _ _ _ _ _ _ _ _ _ hk hv (by simp) (by simp) increment_layout
  have hn := constantModularAddIdealState_correct (List.range' 4 256) _ _ _ 516 0 s hk hv
    List.nodup_range' (by simp) (by simp) (by decide) hf
    (by simp only [List.length_range']; decide +kernel)
    (by rw [increment_bits_value]; decide +kernel) hy
    (by rw [secp256k1ReductionConstant_value]; simp only [List.length_range']; decide +kernel)
  simp only [increment_bits_value] at hn
  refine ⟨hn.1,hn.2,?_,fun ψ => Quantum.AdaptiveCircuit.run_preservesBornMass _ hw ψ,hw,
    increment_metrics.1,increment_metrics.2.1,increment_metrics.2.2,increment_qubits⟩
  intro b hb
  exact controlledConstantModularAdd_branch_correct _ _ _ _ _ _ _ _ _ _ s hk hv
    (by simp) (by simp) increment_layout hc hr ht b hb

end ShorECDLP.Paper2607_13816
