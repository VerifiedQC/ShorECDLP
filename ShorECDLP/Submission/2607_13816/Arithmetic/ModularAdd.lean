import ShorECDLP.Submission.«2607_13816».Arithmetic.UncontrolledCompare
import ShorECDLP.Submission.«2607_13816».Arithmetic.GidneyAdd
import ShorECDLP.Submission.«2607_13816».Arithmetic.Compare
import ShorECDLP.Submission.«2607_13816».Arithmetic.ModularCorrection

/-!
# Controlled quadratic modular addition

The four source stages add a word with overflow, compare the low word with the
modulus, apply the constant correction under the reduction flag, and clear that
flag with a final comparison. The preserved addend supplies borrowed workspace.
-/
namespace ShorECDLP.Paper2607_13816
open Classical
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-- Source `append_ctrl_add_modp_quadratic`. `correction` encodes `2^n - p`.
Only the first `n-1` addend wires are borrowed by the constant-adder stage. -/
def controlledModularAdd (input acc : List Wire) (correction : List Bool) (p : Nat)
    (q c r t f : Wire) : Quantum.AdaptiveCircuit :=
  .unitary (controlledAddCarry input acc q c f)
    ((gidneyCompareGE acc input p c r t f).seq
      ((controlledGidneyAddConst acc (input.take (acc.length - 1)) correction f c r t).seq
        (.unitary (controlledCompareLT acc input q c f) .done)))

private theorem modularAdd_layout (input acc : List Wire) (q c r t f : Wire)
    (h : ([q,c,r,t,f] ++ input ++ acc).Nodup) :
    (q :: c :: f :: input ++ acc).Nodup ∧
    ([c,r,t,f] ++ acc ++ input).Nodup ∧
    ([f,c,r,t] ++ acc ++ input.take (acc.length - 1)).Nodup ∧
    (q :: c :: f :: acc ++ input).Nodup := by
  have hshort : (q :: c :: f :: input ++ acc).Nodup :=
    List.Nodup.sublist
      (((by simp : [q,c,f].Sublist [q,c,r,t,f]).append (List.Sublist.refl input)).append (List.Sublist.refl acc)) h
  have htail : ([c,r,t,f] ++ input ++ acc).Nodup := (List.nodup_cons.mp h).2
  have hswap : ([c,r,t,f] ++ acc ++ input).Nodup := by
    apply (List.Perm.nodup_iff ((List.perm_append_comm (l₁ := input) (l₂ := acc)).append_left [c,r,t,f])).mp
    simpa only [List.append_assoc] using htail
  have hrotate : ([f,c,r,t] ++ acc ++ input).Nodup := by
    apply (List.Perm.nodup_iff ((List.perm_append_comm (l₁ := [c,r,t]) (l₂ := [f])).append_right (acc ++ input))).mp
    simpa only [List.append_assoc] using hswap
  have hadd : ([f,c,r,t] ++ acc ++ input.take (acc.length - 1)).Nodup :=
    List.Nodup.sublist ((List.Sublist.refl ([f,c,r,t] ++ acc)).append (List.take_sublist _ _)) hrotate
  have hlast : (q :: c :: f :: acc ++ input).Nodup := by
    apply (List.Perm.nodup_iff ((List.perm_append_comm (l₁ := input) (l₂ := acc)).append_left [q,c,f])).mp
    simpa only [List.append_assoc] using hshort
  exact ⟨hshort,hswap,hadd,hlast⟩

/-- Each stage respects the shared physical layout. -/
theorem controlledModularAdd_wellFormed (input acc : List Wire) (correction : List Bool) (p : Nat)
    (q c r t f : Wire) (hlen : input.length = acc.length) (hne : 0 < acc.length)
    (hk : acc.length = correction.length) (hnd : ([q,c,r,t,f] ++ input ++ acc).Nodup) :
    (controlledModularAdd input acc correction p q c r t f).WellFormed := by
  have hl := modularAdd_layout input acc q c r t f hnd
  have hd : acc.length = (input.take (acc.length - 1)).length + 1 := by
    rw [List.length_take,hlen,Nat.min_eq_left (Nat.sub_le _ _)]
    omega
  exact ⟨controlledAddCarry_wellFormed input acc q c f hlen hl.1,
    Quantum.AdaptiveCircuit.WellFormed.seq (gidneyCompareGE_wellFormed acc input p c r t f hlen.symm hl.2.1)
      (Quantum.AdaptiveCircuit.WellFormed.seq
        (controlledGidneyAddConst_wellFormed acc _ correction f c r t hk hd hl.2.2.1)
        ⟨controlledCompareLT_wellFormed acc input q c f hlen.symm hl.2.2.2,trivial⟩)⟩

private def modularAddLow (input acc : List Wire) (q c f : Wire) (s : BasisState) : BasisState :=
  run (controlledAddCarry input acc q c f) s

private def modularAddFlagged (input acc : List Wire) (p : Nat) (q c f : Wire) (s : BasisState) : BasisState :=
  let low := modularAddLow input acc q c f s
  upd low f (Bool.xor (low f) (decide (p ≤ boolWordToNat (wireValues acc low))))

/-- The corrected accumulator state with the reduction flag returned to its input value. -/
def modularAddIdealState (input acc : List Wire) (correction : List Bool) (p : Nat)
    (q c f : Wire) (s : BasisState) : BasisState :=
  upd (gidneyAddIdealState acc correction f (modularAddFlagged input acc p q c f s)) f (s f)

private theorem modularAdd_overflow (bs as : List Bool) (hlen : bs.length = as.length) :
    carryAddOverflow false bs as = decide (2 ^ bs.length ≤ boolWordToNat bs + boolWordToNat as) := by
  have hv := carryAddOverflow_value false bs as hlen
  simp only [Bool.toNat_false,Nat.zero_add] at hv
  have hpos : 0 < 2 ^ bs.length := by positivity
  cases hc : carryAddOverflow false bs as with
  | false =>
      rw [hc] at hv
      have hsmall : boolWordToNat bs + boolWordToNat as < 2 ^ bs.length := by
        have hz := Nat.div_eq_zero_iff.mp hv.symm
        omega
      simp [Nat.not_le.mpr hsmall]
  | true =>
      rw [hc] at hv
      have hlarge : 2 ^ bs.length ≤ boolWordToNat bs + boolWordToNat as := by
        by_contra hn
        have hh := Nat.div_eq_of_lt (Nat.lt_of_not_ge hn)
        rw [hh] at hv
        contradiction
      simp [hlarge]

private theorem modularAdd_low_value (input acc : List Wire) (q c f : Wire) (s : BasisState)
    (hlen : input.length = acc.length) (hnd : (q :: c :: f :: input ++ acc).Nodup)
    (hc : s c = false) (hf : s f = false) :
    boolWordToNat (wireValues acc (modularAddLow input acc q c f s)) =
      (boolWordToNat (wireValues acc s) + if s q then boolWordToNat (wireValues input s) else 0) % 2 ^ acc.length ∧
    modularAddLow input acc q c f s f = decide (2 ^ acc.length ≤
      boolWordToNat (wireValues acc s) + if s q then boolWordToNat (wireValues input s) else 0) := by
  have hcorrect := controlledAddCarry_correct input acc q c f s hlen hnd
  have hv := controlledAddCarry_value input acc q c f s hlen hnd
  have ho := modularAdd_overflow (wireValues input s) (wireValues acc s) (by simpa [wireValues] using hlen)
  have hy : boolWordToNat (wireValues acc s) < 2 ^ acc.length := by
    simpa only [wireValues,List.length_map] using boolWordToNat_lt_pow_two (wireValues acc s)
  constructor
  · cases hq : s q
    · simpa [modularAddLow,hq,hc,Nat.mod_eq_of_lt hy] using hv
    · simpa [modularAddLow,hq,hc,hlen,Nat.add_comm] using hv
  · change run (controlledAddCarry input acc q c f) s f = _
    rw [hcorrect.2.2.1,hc,hf,ho]
    cases hq : s q <;> simp [hq,wireValues,hlen,Nat.add_comm,Nat.not_le.mpr hy]
    exact hy

private theorem modularAdd_geometry (input acc : List Wire) (q c r t f : Wire)
    (hnd : ([q,c,r,t,f] ++ input ++ acc).Nodup) :
    (∀ w ∈ [q,c,r,t] ++ input, w ∉ f :: acc) ∧ f ∉ acc ∧ acc.Nodup := by
  have hp := (List.nodup_append.mp hnd).1
  have hs := (List.nodup_append.mp hnd).2.2
  have hrot : ([f,q,c,r,t] ++ input).Nodup := by
    apply (List.Perm.nodup_iff ((List.perm_append_comm (l₁ := [q,c,r,t]) (l₂ := [f])).append_right input)).mp
    exact hp
  have hfirst : f ∉ [q,c,r,t] ++ input := (List.nodup_cons.mp hrot).1
  refine ⟨?_,?_,(List.nodup_append.mp hnd).2.1⟩
  · intro w hw
    have hw' : w ∈ [q,c,r,t,f] ++ input := by
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil] at hw ⊢
      tauto
    intro hm
    rcases List.mem_cons.mp hm with he | ha
    · subst w; exact hfirst hw
    · exact hs w hw' w ha rfl
  · intro hf
    exact hs f (by simp) f hf rfl

private theorem modularAdd_intermediate_frame (input acc : List Wire) (correction : List Bool) (p : Nat)
    (q c r t f : Wire) (s : BasisState) (hlen : input.length = acc.length)
    (hk : acc.length = correction.length) (hnd : ([q,c,r,t,f] ++ input ++ acc).Nodup) :
    (∀ w, w ∉ f :: acc → modularAddLow input acc q c f s w = s w) ∧
    (∀ w, w ∉ f :: acc → modularAddFlagged input acc p q c f s w = s w) ∧
    (∀ w, w ∉ f :: acc →
      gidneyAddIdealState acc correction f (modularAddFlagged input acc p q c f s) w = s w) := by
  have hl := modularAdd_layout input acc q c r t f hnd
  have hg := modularAdd_geometry input acc q c r t f hnd
  have hlow := (controlledAddCarry_correct input acc q c f s hlen hl.1).2.2.2
  have hflag : ∀ w, w ∉ f :: acc → modularAddFlagged input acc p q c f s w = s w := by
    intro w hw
    have hwf : w ≠ f := fun he => hw (by simp [he])
    simp only [modularAddFlagged,upd,if_neg hwf]
    exact hlow w hw
  have hmid := (gidneyAddIdealState_correct acc correction f
    (modularAddFlagged input acc p q c f s) hk hg.2.2).2
  refine ⟨hlow,hflag,?_⟩
  intro w hw
  have hwa : w ∉ acc := fun ha => hw (by simp [ha])
  exact (hmid w hwa).trans (hflag w hw)

/-- The ideal output changes only accumulator wires. -/
private theorem modularAddIdealState_frame (input acc : List Wire) (correction : List Bool) (p : Nat)
    (q c r t f : Wire) (s : BasisState) (hlen : input.length = acc.length)
    (hk : acc.length = correction.length) (hnd : ([q,c,r,t,f] ++ input ++ acc).Nodup) :
    ∀ w, w ∉ acc → modularAddIdealState input acc correction p q c f s w = s w := by
  have hm := (modularAdd_intermediate_frame input acc correction p q c r t f s hlen hk hnd).2.2
  intro w hw
  by_cases hf : w = f
  · subst w; simp [modularAddIdealState]
  · simp only [modularAddIdealState,upd,if_neg hf]
    exact hm w (by simp [hf,hw])

private theorem modularAdd_word_upd (ws : List Wire) (s : BasisState) (f : Wire) (b : Bool)
    (h : f ∉ ws) : wireValues ws (upd s f b) = wireValues ws s := by
  apply List.map_congr_left
  intro w hw
  have hn : w ≠ f := by intro he; subst w; exact h hw
  simp [upd,hn]

private theorem modularAdd_corrected (input acc : List Wire) (correction : List Bool) (p : Nat)
    (q c r t f : Wire) (s : BasisState) (hlen : input.length = acc.length)
    (hk : acc.length = correction.length) (hnd : ([q,c,r,t,f] ++ input ++ acc).Nodup)
    (hc : s c = false) (hf : s f = false) (hp : p < 2 ^ acc.length)
    (hx : boolWordToNat (wireValues input s) < p) (hy : boolWordToNat (wireValues acc s) < p)
    (hconstant : boolWordToNat correction = 2 ^ acc.length - p) :
    let mid := gidneyAddIdealState acc correction f (modularAddFlagged input acc p q c f s)
    boolWordToNat (wireValues acc mid) =
      (boolWordToNat (wireValues acc s) + if s q then boolWordToNat (wireValues input s) else 0) % p ∧
      run (controlledCompareLT acc input q c f) mid = modularAddIdealState input acc correction p q c f s := by
  have hl := modularAdd_layout input acc q c r t f hnd
  have hg := modularAdd_geometry input acc q c r t f hnd
  have hframe := modularAdd_intermediate_frame input acc correction p q c r t f s hlen hk hnd
  have hlow := modularAdd_low_value input acc q c f s hlen hl.1 hc hf
  let total := boolWordToNat (wireValues acc s) + if s q then boolWordToNat (wireValues input s) else 0
  let flag := Bool.xor (decide (2 ^ acc.length ≤ total)) (decide (p ≤ total % 2 ^ acc.length))
  have hword : boolWordToNat (wireValues acc (modularAddFlagged input acc p q c f s)) = total % 2 ^ acc.length := by
    unfold modularAddFlagged
    rw [modularAdd_word_upd _ _ f _ hg.2.1]
    exact hlow.1
  have hflag : modularAddFlagged input acc p q c f s f = flag := by
    simp only [modularAddFlagged,upd,↓reduceIte,hlow.1,hlow.2]
    rfl
  let mid := gidneyAddIdealState acc correction f (modularAddFlagged input acc p q c f s)
  have hadd := gidneyAddIdealState_correct acc correction f (modularAddFlagged input acc p q c f s) hk hg.2.2
  have hmath := modularCorrection_correct (2 ^ acc.length) p
    (boolWordToNat (wireValues input s)) (boolWordToNat (wireValues acc s)) (s q) hp hx hy
  change ((total % 2 ^ acc.length + if flag then 2 ^ acc.length - p else 0) % 2 ^ acc.length = total % p) ∧
    _ ∧ _ at hmath
  have hvalue : boolWordToNat (wireValues acc mid) = total % p := by
    change boolWordToNat (wireValues acc (gidneyAddIdealState acc correction f _)) = _
    rw [hadd.1,hword,hflag,hconstant]
    exact hmath.1
  have hmflag : mid f = flag := (hadd.2 f hg.2.1).trans hflag
  have hmq : mid q = s q := hframe.2.2 q (hg.1 q (by simp))
  have hmc : mid c = false := (hframe.2.2 c (hg.1 c (by simp))).trans hc
  have hminput : wireValues input mid = wireValues input s := by
    apply List.map_congr_left
    intro w hw
    exact hframe.2.2 w (hg.1 w (by simp [hw]))
  refine ⟨hvalue,?_⟩
  change run (controlledCompareLT acc input q c f) mid = _
  rw [controlledCompareLT_correct acc input q c f mid hlen.symm hl.2.2.2 hmc,
    hmflag,hmq,hvalue,hminput]
  have hclear : Bool.xor flag (s q && decide (total % p < boolWordToNat (wireValues input s))) = false := by
    have hh := hmath.2.2
    change Bool.xor flag (s q && decide
      ((total % 2 ^ acc.length + if flag then 2 ^ acc.length - p else 0) % 2 ^ acc.length <
        boolWordToNat (wireValues input s))) = false at hh
    rw [hmath.1] at hh
    exact hh
  rw [hclear]
  simp only [modularAddIdealState,hf]
  rfl

/-- The ideal output is the canonical controlled modular sum and preserves its frame. -/
theorem modularAddIdealState_correct (input acc : List Wire) (correction : List Bool) (p : Nat)
    (q c r t f : Wire) (s : BasisState) (hlen : input.length = acc.length)
    (hk : acc.length = correction.length) (hnd : ([q,c,r,t,f] ++ input ++ acc).Nodup)
    (hc : s c = false) (hf : s f = false) (hp : p < 2 ^ acc.length)
    (hx : boolWordToNat (wireValues input s) < p) (hy : boolWordToNat (wireValues acc s) < p)
    (hconstant : boolWordToNat correction = 2 ^ acc.length - p) :
    boolWordToNat (wireValues acc (modularAddIdealState input acc correction p q c f s)) =
      (boolWordToNat (wireValues acc s) + if s q then boolWordToNat (wireValues input s) else 0) % p ∧
      ∀ w, w ∉ acc → modularAddIdealState input acc correction p q c f s w = s w := by
  refine ⟨?_,modularAddIdealState_frame input acc correction p q c r t f s hlen hk hnd⟩
  unfold modularAddIdealState
  rw [modularAdd_word_upd _ _ f _ (modularAdd_geometry input acc q c r t f hnd).2.1]
  exact (modularAdd_corrected input acc correction p q c r t f s hlen hk hnd hc hf hp hx hy hconstant).1

/-- Each branch implements controlled modular addition with a positive,
input-independent amplitude and complete restoration outside the accumulator. -/
theorem controlledModularAdd_branch_correct (input acc : List Wire) (correction : List Bool) (p : Nat)
    (q c r t f : Wire) (s : BasisState) (hlen : input.length = acc.length) (hne : 0 < acc.length)
    (hk : acc.length = correction.length) (hnd : ([q,c,r,t,f] ++ input ++ acc).Nodup)
    (hc : s c = false) (hr : s r = false) (ht : s t = false) (hf : s f = false)
    (hp : p < 2 ^ acc.length) (hx : boolWordToNat (wireValues input s) < p)
    (hy : boolWordToNat (wireValues acc s) < p) (hconstant : boolWordToNat correction = 2 ^ acc.length - p)
    (branch : Quantum.InstrumentBranch) (hb : branch ∈ (controlledModularAdd input acc correction p q c r t f).run) :
    let m := acc.length + if correction.all (fun k => !k) then 0 else (input.take (acc.length - 1)).length
    branch.history.length = m ∧ branch.kraus (Quantum.ket s) = Quantum.registerXResetMagnitude m •
      Quantum.ket (modularAddIdealState input acc correction p q c f s) := by
  have hl := modularAdd_layout input acc q c r t f hnd
  have hg := modularAdd_geometry input acc q c r t f hnd
  have hframe := modularAdd_intermediate_frame input acc correction p q c r t f s hlen hk hnd
  have hd : acc.length = (input.take (acc.length - 1)).length + 1 := by
    rw [List.length_take,hlen,Nat.min_eq_left (Nat.sub_le _ _)]
    omega
  obtain ⟨after,ha,hh,hkBranch⟩ := gidneyUnitaryBranch (controlledAddCarry input acc q c f) _ branch hb
  simp only [Quantum.AdaptiveCircuit.run_seq,Quantum.Instrument.seq,List.mem_flatMap,List.mem_map,
    Quantum.AdaptiveCircuit.run_unitary_done,List.mem_singleton] at ha
  obtain ⟨compareBranch,hcompare,addTail,haddTail,rfl⟩ := ha
  obtain ⟨addBranch,haddBranch,last,rfl,rfl⟩ := haddTail
  have hshort : ¬ (p = 0 ∨ 2 ^ acc.length ≤ p) := by omega
  have hcmp := gidneyCompareGE_branch_correct acc input p c r t f (modularAddLow input acc q c f s)
    hlen.symm hl.2.1
    ((hframe.1 c (hg.1 c (by simp))).trans hc)
    ((hframe.1 r (hg.1 r (by simp))).trans hr)
    ((hframe.1 t (hg.1 t (by simp))).trans ht) compareBranch hcompare
  simp only [if_neg hshort] at hcmp
  have hadd := controlledGidneyAddConst_branch_correct acc (input.take (acc.length - 1)) correction f c r t
    (modularAddFlagged input acc p q c f s) hk hd hl.2.2.1
    ((hframe.2.1 c (hg.1 c (by simp))).trans hc)
    ((hframe.2.1 r (hg.1 r (by simp))).trans hr)
    ((hframe.2.1 t (hg.1 t (by simp))).trans ht) addBranch haddBranch
  have hlast := (modularAdd_corrected input acc correction p q c r t f s hlen hk hnd hc hf hp hx hy hconstant).2
  dsimp only at hadd ⊢
  constructor
  · rw [hh]
    simp only [Quantum.InstrumentBranch.seq,List.length_append,List.length_nil,Nat.add_zero,hcmp.1,hadd.1]
  · rw [hkBranch]
    simp only [Quantum.InstrumentBranch.seq,LinearMap.comp_apply]
    rw [Quantum.run_ket_agrees_classical _ _ (controlledAddCarry_HPFree input acc q c f)]
    change Quantum.run (controlledCompareLT acc input q c f)
      (addBranch.kraus (compareBranch.kraus (Quantum.ket (modularAddLow input acc q c f s)))) = _
    rw [hcmp.2,map_smul]
    change Quantum.run (controlledCompareLT acc input q c f)
      (Quantum.registerXResetMagnitude acc.length • addBranch.kraus (Quantum.ket (modularAddFlagged input acc p q c f s))) = _
    rw [hadd.2,map_smul,map_smul,Quantum.run_ket_agrees_classical _ _ (controlledCompareLT_HPFree acc input q c f),hlast]
    simp only [smul_smul,Quantum.registerXResetMagnitude,← pow_add]

private theorem modularGateCount_seq (cost : Gate → Nat) (a b : Quantum.AdaptiveCircuit) :
    gidneyGateCount cost (a.seq b) = gidneyGateCount cost a + gidneyGateCount cost b := by
  induction a with
  | done => simp [Quantum.AdaptiveCircuit.seq,gidneyGateCount]
  | unitary gates next ih => simp [Quantum.AdaptiveCircuit.seq,gidneyGateCount,ih,Nat.add_assoc]
  | xMeasureReset w l r ihl ihr =>
      simp [Quantum.AdaptiveCircuit.seq,gidneyGateCount,ihl,ihr,max_add_add_right]

private theorem modularMeasurements_seq (a b : Quantum.AdaptiveCircuit) :
    (a.seq b).measurementCount = a.measurementCount + b.measurementCount := by
  induction a with
  | done => simp [Quantum.AdaptiveCircuit.seq,Quantum.AdaptiveCircuit.measurementCount]
  | unitary gates next ih => exact ih
  | xMeasureReset w l r ihl ihr =>
      simp [Quantum.AdaptiveCircuit.seq,Quantum.AdaptiveCircuit.measurementCount,ihl,ihr,
        max_add_add_right,Nat.add_assoc]

private theorem modularWires_seq (a b : Quantum.AdaptiveCircuit) (w : Wire) :
    w ∈ (a.seq b).wires ↔ w ∈ a.wires ∨ w ∈ b.wires := by
  induction a with
  | done => simp [Quantum.AdaptiveCircuit.seq,Quantum.AdaptiveCircuit.wires]
  | unitary gates next ih => simp [Quantum.AdaptiveCircuit.seq,Quantum.AdaptiveCircuit.wires,ih,or_assoc]
  | xMeasureReset t l r ihl ihr =>
      simp only [Quantum.AdaptiveCircuit.seq,Quantum.AdaptiveCircuit.wires,List.mem_cons,List.mem_append,ihl,ihr]
      tauto

/-- Concrete 256-bit controlled modular addition, with a shared borrowed addend. -/
def secp256k1ModularAdd : Quantum.AdaptiveCircuit :=
  controlledModularAdd (List.range' 260 256) (List.range' 4 256)
    secp256k1ReductionConstantBits (2 ^ 256 - (2 ^ 32 + 977)) 516 1 2 3 0

private def modularProductionCompare : Quantum.AdaptiveCircuit :=
  gidneyCompareGE (List.range' 4 256) (List.range' 260 256)
    (2 ^ 256 - (2 ^ 32 + 977)) 1 2 3 0

private def modularProductionQ : Wire :=
  ([1,2,3,0] ++ List.range' 4 256 ++ List.range' 260 256).sum + 1

set_option maxRecDepth 10000 in
private theorem modularProduction_core : modularProductionCompare =
    constantControlProgram modularProductionQ
      (controlledGidneyCompareCarry (List.range' 4 256) (List.range' 260 256)
        secp256k1ReductionConstantBits modularProductionQ 1 2 3 0) := by
  unfold modularProductionCompare gidneyCompareGE
  dsimp only
  unfold controlledGidneyCompareGE
  rw [if_neg (by decide)]
  simp only [List.length_range']
  rw [if_neg (by decide),Nat.sub_sub_self (by decide : 2 ^ 32 + 977 ≤ 2 ^ 256)]
  rfl

private theorem modularProduction_fresh :
    modularProductionQ ∉ [1,2,3,0] ++ List.range' 4 256 ++ List.range' 260 256 :=
  by
    intro h
    have hh : modularProductionQ ≤ ([1,2,3,0] ++ List.range' 4 256 ++ List.range' 260 256).sum := List.le_sum_of_mem h
    exact (Nat.not_succ_le_self (([1,2,3,0] ++ List.range' 4 256 ++ List.range' 260 256).sum)) hh

set_option maxRecDepth 100000 in
private theorem modularProduction_metrics :
    gidneyToffoliCount modularProductionCompare = 767 ∧
    modularProductionCompare.tCount = 5369 ∧
    modularProductionCompare.measurementCount = 256 := by
  have h := controlledGidneyCompareCarry_metrics 4 260 modularProductionQ 1 2 3 0
    (List.range' 5 255) (List.range' 261 255) true
    ((List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977))) (by simp) (by simp)
  rw [modularProduction_core,gidneyToffoliCount_constantControl,
    constantControlProgram_tCount,constantControlProgram_measurements,
    show List.range' 4 256 = 4 :: List.range' 5 255 from rfl,
    show List.range' 260 256 = 260 :: List.range' 261 255 from rfl,
    show secp256k1ReductionConstantBits = true ::
      (List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977)) from rfl]
  simpa only [List.length_range'] using h

set_option maxRecDepth 100000 in
private theorem modularProduction_cnot : gidneyCnotCount modularProductionCompare = 1537 := by
  rw [modularProduction_core,
    show List.range' 4 256 = 4 :: List.range' 5 255 from rfl,
    show List.range' 260 256 = 260 :: List.range' 261 255 from rfl,
    show secp256k1ReductionConstantBits = true ::
      (List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977)) from rfl]
  exact controlledGidneyCompareCarry_uncontrolled_cnot 4 260 modularProductionQ 1 2 3 0
    (List.range' 5 255) (List.range' 261 255) true
    ((List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977)))
    (by simp) (by simp) modularProduction_fresh

private theorem modularProduction_decompose : secp256k1ModularAdd =
    .unitary (controlledAddCarry (List.range' 260 256) (List.range' 4 256) 516 1 0)
      (modularProductionCompare.seq (secp256k1GidneyAdd.seq
        (.unitary (controlledCompareLT (List.range' 4 256) (List.range' 260 256) 516 1 0) .done))) := by
  unfold secp256k1ModularAdd controlledModularAdd
  rw [show (List.range' 4 256).length - 1 = 255 from rfl,
    show (List.range' 260 256).take 255 = List.range' 260 255 from rfl]
  rfl

private theorem modularToffoli_unitary (g : Circuit) (a : Quantum.AdaptiveCircuit) :
    gidneyToffoliCount (.unitary g a) = eeaToffoliCount g + gidneyToffoliCount a := rfl

private theorem modularCnot_unitary (g : Circuit) (a : Quantum.AdaptiveCircuit) :
    gidneyCnotCount (.unitary g a) = eeaCnotCount g + gidneyCnotCount a := rfl

private theorem modularProduction_counts :
    gidneyToffoliCount secp256k1ModularAdd = 2813 ∧
    gidneyCnotCount secp256k1ModularAdd = 4929 ∧
    secp256k1ModularAdd.tCount = 19691 ∧
    secp256k1ModularAdd.measurementCount = 511 := by
  have ha := secp256k1GidneyAdd_correct_resources (fun _ => false) rfl rfl rfl
  have hb := controlledCompareLT_counts 4 (List.range' 5 255) (List.range' 260 256) 516 1 0 (by simp)
  change eeaToffoliCount (controlledCompareLT (List.range' 4 256) (List.range' 260 256) 516 1 0) = 513 ∧
    eeaCnotCount (controlledCompareLT (List.range' 4 256) (List.range' 260 256) 516 1 0) = 1024 ∧
    eeaXCount (controlledCompareLT (List.range' 4 256) (List.range' 260 256) 516 1 0) = 516 ∧
    tCount (controlledCompareLT (List.range' 4 256) (List.range' 260 256) 516 1 0) = 3591 at hb
  have haddT := controlledAddCarry_toffoliCount (List.range' 260 256) (List.range' 4 256) 516 1 0 (by simp)
  have haddC := controlledAddCarry_cnotCount (List.range' 260 256) (List.range' 4 256) 516 1 0 (by simp)
  have haddCost := controlledAddCarry_tCount (List.range' 260 256) (List.range' 4 256) 516 1 0 (by simp)
  have hseqT (a b : Quantum.AdaptiveCircuit) : (a.seq b).tCount = a.tCount + b.tCount := by
    simpa only [gidneyGateCount_tCount] using modularGateCount_seq tCost a b
  have hseqCCX (a b : Quantum.AdaptiveCircuit) : gidneyToffoliCount (a.seq b) = gidneyToffoliCount a + gidneyToffoliCount b := modularGateCount_seq _ a b
  have hseqCX (a b : Quantum.AdaptiveCircuit) : gidneyCnotCount (a.seq b) = gidneyCnotCount a + gidneyCnotCount b := modularGateCount_seq _ a b
  rw [modularProduction_decompose]
  constructor
  · rw [modularToffoli_unitary,hseqCCX,hseqCCX,modularToffoli_unitary,
      haddT,modularProduction_metrics.1,ha.2.2.2.2.2.1,hb.1]
    rfl
  constructor
  · rw [modularCnot_unitary,hseqCX,hseqCX,modularCnot_unitary,
      haddC,modularProduction_cnot,ha.2.2.2.2.2.2.1,hb.2.1]
    rfl
  constructor
  · rw [Quantum.AdaptiveCircuit.tCount,hseqT,hseqT,Quantum.AdaptiveCircuit.tCount,
      haddCost,modularProduction_metrics.2.1,ha.2.2.2.2.2.2.2.1,hb.2.2.2]
    rfl
  · rw [Quantum.AdaptiveCircuit.measurementCount,modularMeasurements_seq,modularMeasurements_seq,
      Quantum.AdaptiveCircuit.measurementCount,modularProduction_metrics.2.2,ha.2.2.2.2.2.2.2.2.1]
    rfl

set_option maxRecDepth 100000 in
private theorem modularProduction_compare_wires (w : Wire) :
    w ∈ modularProductionCompare.wires ↔ w ∈ [1,2,3,0] ++ List.range' 4 256 ++ List.range' 260 256 := by
  rw [modularProduction_core,constantControlProgram_wires _ _
    (controlledGidneyCompareCarry_controlSafe _ _ _ _ _ _ _ _ modularProduction_fresh),
    show List.range' 4 256 = 4 :: List.range' 5 255 from rfl,
    show List.range' 260 256 = 260 :: List.range' 261 255 from rfl,
    show secp256k1ReductionConstantBits = true ::
      (List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977)) from rfl,
    controlledGidneyCompareCarry_wires _ _ _ _ _ _ _ _ _ _ (by simp) (by simp)]
  have hf := modularProduction_fresh
  change (w ∈ modularProductionQ :: ([1,2,3,0] ++ List.range' 4 256 ++ List.range' 260 256) ∧ w ≠ modularProductionQ) ↔ w ∈ [1,2,3,0] ++ List.range' 4 256 ++ List.range' 260 256
  by_cases hw : w = modularProductionQ
  · subst w; simpa only [ne_eq,not_true_eq_false,and_false,false_iff] using hf
  · simp only [List.mem_cons]
    constructor
    · intro h; exact h.1.resolve_left hw
    · intro h; exact ⟨Or.inr h,hw⟩

set_option maxRecDepth 100000 in
private theorem modularProduction_add_wires (w : Wire) :
    w ∈ secp256k1GidneyAdd.wires ↔ w ∈ [0,1,2,3] ++ List.range' 4 256 ++ List.range' 260 255 := by
  unfold secp256k1GidneyAdd
  rw [show List.range' 4 256 = 4 :: List.range' 5 255 from rfl,
    show List.range' 260 255 = 260 :: List.range' 261 254 from rfl,
    show secp256k1ReductionConstantBits = true ::
      (List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977)) from rfl]
  exact controlledGidneyAddConst_wires _ _ _ _ _ _ _ _ _ (by simp) (by simp) w

set_option maxRecDepth 100000 in
private theorem modularProduction_wires (w : Wire) :
    w ∈ secp256k1ModularAdd.wires ↔ w ∈ List.range' 0 517 := by
  rw [modularProduction_decompose]
  simp only [Quantum.AdaptiveCircuit.wires,List.mem_append,modularWires_seq,
    modularProduction_compare_wires,modularProduction_add_wires,List.not_mem_nil,or_false]
  have hfirst := controlledAddCarry_usesOnly (List.range' 260 256) (List.range' 4 256) 516 1 0
  have hlast := controlledCompareLT_wires 4 (List.range' 5 255) (List.range' 260 256) 516 1 0 w (by simp)
  change (w ∈ circuitWires _ ∨ _ ∨ _ ∨ w ∈ circuitWires
    (controlledCompareLT (4 :: List.range' 5 255) _ 516 1 0)) ↔ _
  rw [hlast]
  constructor
  · intro h
    rcases h with h | h | h | h
    · obtain ⟨g,hg,hw⟩ := List.mem_flatMap.mp h
      have hh := hfirst g hg w hw
      simp at hh ⊢
      dsimp only [Wire] at *
      omega
    all_goals simp at h ⊢; dsimp only [Wire] at *; omega
  · intro h
    simp at h
    by_cases hw : w = 516
    · subst w; right; right; right; simp
    · right; left
      simp
      dsimp only [Wire] at *
      omega

private theorem modularProduction_qubits : secp256k1ModularAdd.qubitCount = 517 := by
  have heq : secp256k1ModularAdd.wires.dedup.toFinset = (List.range' 0 517).toFinset := by
    ext w; simpa only [List.mem_toFinset,List.mem_dedup] using modularProduction_wires w
  have hc := congrArg Finset.card heq
  simpa only [List.toFinset_card_of_nodup (List.nodup_dedup _),
    List.toFinset_card_of_nodup (List.nodup_range'),List.length_range'] using hc

set_option maxHeartbeats 4000000 in
private theorem modularProduction_layout :
    ([516,1,2,3,0] ++ List.range' 260 256 ++ List.range' 4 256).Nodup := by decide

/-- Same-circuit certificate: controlled addition modulo the secp256k1 prime,
complete frame restoration, normalized measurement branches, and exact resources.
The input word is borrowed and restored; all four auxiliary wires start and end clean. -/
theorem secp256k1ModularAdd_correct_resources (s : BasisState)
    (hc : s 1 = false) (hr : s 2 = false) (ht : s 3 = false) (hf : s 0 = false)
    (hx : boolWordToNat (wireValues (List.range' 260 256) s) < 2 ^ 256 - (2 ^ 32 + 977))
    (hy : boolWordToNat (wireValues (List.range' 4 256) s) < 2 ^ 256 - (2 ^ 32 + 977)) :
    let after := modularAddIdealState (List.range' 260 256) (List.range' 4 256)
      secp256k1ReductionConstantBits (2 ^ 256 - (2 ^ 32 + 977)) 516 1 0 s
    boolWordToNat (wireValues (List.range' 4 256) after) =
      (boolWordToNat (wireValues (List.range' 4 256) s) +
        if s 516 then boolWordToNat (wireValues (List.range' 260 256) s) else 0) % (2 ^ 256 - (2 ^ 32 + 977)) ∧
    (∀ w, w ∉ List.range' 4 256 → after w = s w) ∧
    (∀ branch ∈ secp256k1ModularAdd.run, branch.history.length = 511 ∧
      branch.kraus (Quantum.ket s) = Quantum.registerXResetMagnitude 511 • Quantum.ket after) ∧
    Quantum.Instrument.bornMass secp256k1ModularAdd.run (Quantum.ket s) = 1 ∧
    secp256k1ModularAdd.WellFormed ∧
    gidneyToffoliCount secp256k1ModularAdd = 2813 ∧
    gidneyCnotCount secp256k1ModularAdd = 4929 ∧
    secp256k1ModularAdd.tCount = 19691 ∧
    secp256k1ModularAdd.measurementCount = 511 ∧
    secp256k1ModularAdd.qubitCount = 517 := by
  have hlen : (List.range' 260 256).length = (List.range' 4 256).length := by simp
  have hne : 0 < (List.range' 4 256).length := by simp
  have hk : (List.range' 4 256).length = secp256k1ReductionConstantBits.length := by simp [secp256k1ReductionConstantBits]
  have hp : 2 ^ 256 - (2 ^ 32 + 977) < 2 ^ (List.range' 4 256).length := by decide
  have hv : boolWordToNat secp256k1ReductionConstantBits =
      2 ^ (List.range' 4 256).length - (2 ^ 256 - (2 ^ 32 + 977)) := by
    rw [secp256k1ReductionConstant_value]; decide
  have hw := controlledModularAdd_wellFormed _ _ _ (2 ^ 256 - (2 ^ 32 + 977))
    516 1 2 3 0 hlen hne hk modularProduction_layout
  have ha := modularAddIdealState_correct _ _ _ _ 516 1 2 3 0 s hlen hk modularProduction_layout hc hf hp hx hy hv
  dsimp only
  refine ⟨ha.1,ha.2,?_,?_,hw,modularProduction_counts.1,modularProduction_counts.2.1,
    modularProduction_counts.2.2.1,modularProduction_counts.2.2.2,modularProduction_qubits⟩
  · intro branch hb
    have h := controlledModularAdd_branch_correct _ _ _ _ 516 1 2 3 0 s hlen hne hk
      modularProduction_layout hc hr ht hf hp hx hy hv branch hb
    have hz : secp256k1ReductionConstantBits.all (fun k => !k) = false := by decide
    simpa only [List.length_range',List.length_take,hz,Bool.false_eq_true,↓reduceIte] using h
  · exact Quantum.AdaptiveCircuit.run_bornMass_eq_one _ hw _ (Quantum.normSq_ket s)

end ShorECDLP.Paper2607_13816
