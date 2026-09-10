import ShorECDLP.Submission.«2607_13816».Arithmetic.HornerMul

/-! # Controlled constant-minus wrapper

The EEA wrapper implements `p - x` using controlled bitwise complement,
addition of one, then addition of `p`. Both additions retain the source's
measurement-assisted implementation and restore borrowed storage.
-/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section

def controlledComplement (input : List Wire) (q : Wire) : Circuit :=
  input.map (Gate.CX q)

theorem controlledComplement_state (input : List Wire) (q : Wire)
    (s : BasisState) (hnd : input.Nodup) (hq : q ∉ input) :
    run (controlledComplement input q) s =
      fun w => if w ∈ input then s w ^^ s q else s w := by
  induction input generalizing s with
  | nil => rfl
  | cons a rest ih =>
    have ha := (List.nodup_cons.mp hnd).1
    have ht := (List.nodup_cons.mp hnd).2
    have hqa : q ≠ a := by intro h; exact hq (by simp [h])
    have hqr : q ∉ rest := fun h => hq (by simp [h])
    change run (Gate.CX q a :: controlledComplement rest q) s = _
    rw [Classical.run_cons,ih _ ht hqr]
    funext w
    by_cases hwa : w = a
    · subst w; simp [ha,Classical.applyGate,upd, Bool.xor_comm]
    · simp [hwa,Classical.applyGate,upd,hqa]

/-- Source wrapper: controlled complement, add one, add the modulus. -/
def controlledConstMinus (input dirty : List Wire) (modulus : List Bool)
    (q c r t : Wire) : AdaptiveCircuit :=
  .unitary (controlledComplement input q)
    ((controlledGidneyAddConst input dirty
      ((List.range input.length).map (Nat.testBit 1)) q c r t).seq
      (controlledGidneyAddConst input dirty modulus q c r t))

/-- Direct arithmetic state of the same three source stages. -/
def constMinusIdealState (input : List Wire) (modulus : List Bool)
    (q : Wire) (s : BasisState) : BasisState :=
  gidneyAddIdealState input modulus q
    (gidneyAddIdealState input ((List.range input.length).map (Nat.testBit 1)) q
      (fun w => if w ∈ input then s w ^^ s q else s w))

/-- On a canonical residue, the wrapper conditionally replaces it by `p - x`
and preserves every other wire. -/
theorem constMinusIdealState_correct (input : List Wire) (modulus : List Bool)
    (q p : Nat) (s : BasisState) (hn : 0 < input.length)
    (hk : input.length = modulus.length) (hnd : input.Nodup) (hq : q ∉ input)
    (hp : p < 2 ^ input.length) (hm : boolWordToNat modulus = p)
    (hx : boolWordToNat (wireValues input s) ≤ p) :
    boolWordToNat (wireValues input (constMinusIdealState input modulus q s)) =
      (if s q then p - boolWordToNat (wireValues input s)
        else boolWordToNat (wireValues input s)) ∧
    (∀ w, w ∉ input → constMinusIdealState input modulus q s w = s w) := by
  let flipped : BasisState := fun w => if w ∈ input then s w ^^ s q else s w
  let increment := (List.range input.length).map (Nat.testBit 1)
  have hone : boolWordToNat increment = 1 :=
    gidneyCompareBits_value input.length 1 (by exact Nat.one_lt_two_pow hn.ne')
  have hfirst := gidneyAddIdealState_correct input increment q flipped (by simp [increment]) hnd
  have hsecond := gidneyAddIdealState_correct input modulus q
    (gidneyAddIdealState input increment q flipped) hk hnd
  have hflipq : flipped q = s q := by simp [flipped,hq]
  constructor
  · change boolWordToNat (wireValues input
      (gidneyAddIdealState input modulus q (gidneyAddIdealState input increment q flipped))) = _
    rw [hsecond.1,hfirst.1,hfirst.2 q hq,hflipq,hone,hm]
    have hsmall : boolWordToNat (wireValues input s) < 2 ^ input.length := by omega
    cases hs : s q with
    | false =>
      have he : flipped = s := by funext w; simp [flipped,hs]
      simp [he,Nat.mod_eq_of_lt hsmall]
    | true =>
      have he : wireValues input flipped = (wireValues input s).map Bool.not := by
        simp only [wireValues,List.map_map]
        apply List.map_congr_left
        intro w hw
        simp [flipped,hs,hw]
      rw [he]
      have hcomp := boolWordToNat_map_not_add (wireValues input s)
      have hlen : (wireValues input s).length = input.length := by simp [wireValues]
      rw [hlen] at hcomp
      simp only [↓reduceIte]
      rw [Nat.mod_add_mod]
      have heq : boolWordToNat ((wireValues input s).map Bool.not) + 1 + p =
          2 ^ input.length + (p - boolWordToNat (wireValues input s)) := by
        have hpos := Nat.two_pow_pos input.length
        omega
      rw [heq,Nat.add_mod_left,Nat.mod_eq_of_lt (by omega)]
  · intro w hw
    exact (hsecond.2 w hw).trans ((hfirst.2 w hw).trans (by simp [flipped,hw]))

/-- Two executions restore every wire, including arbitrary borrowed storage. -/
theorem constMinusIdealState_involutive (input : List Wire) (modulus : List Bool)
    (q p : Nat) (s : BasisState) (hn : 0 < input.length)
    (hk : input.length = modulus.length) (hnd : input.Nodup) (hq : q ∉ input)
    (hp : p < 2 ^ input.length) (hm : boolWordToNat modulus = p)
    (hx : boolWordToNat (wireValues input s) ≤ p) :
    constMinusIdealState input modulus q (constMinusIdealState input modulus q s) = s := by
  have hfirst := constMinusIdealState_correct input modulus q p s hn hk hnd hq hp hm hx
  have hsmall : boolWordToNat (wireValues input (constMinusIdealState input modulus q s)) ≤ p := by
    rw [hfirst.1]; split <;> omega
  have hsecond := constMinusIdealState_correct input modulus q p _ hn hk hnd hq hp hm hsmall
  have hv : boolWordToNat (wireValues input
      (constMinusIdealState input modulus q (constMinusIdealState input modulus q s))) =
      boolWordToNat (wireValues input s) := by
    rw [hsecond.1,hfirst.2 q hq,hfirst.1]
    split <;> omega
  have hw := boolWordToNat_injective_of_length (by simp [wireValues]) hv
  funext w
  by_cases h : w ∈ input
  · exact List.map_inj_left.mp hw w h
  · exact (hsecond.2 w h).trans (hfirst.2 w h)

private theorem constMinus_geometry (input dirty : List Wire) (q c r t : Wire)
    (hnd : ([q,c,r,t] ++ input ++ dirty).Nodup) :
    input.Nodup ∧ (∀ w ∈ [q,c,r,t], w ∉ input) := by
  have hleft := (List.nodup_append.mp hnd).1
  have hparts := List.nodup_append.mp hleft
  refine ⟨hparts.2.1,?_⟩
  intro w hw hi
  exact hparts.2.2 w hw w hi rfl

/-- Every source measurement branch realizes the direct three-stage ideal state. -/
theorem controlledConstMinus_branch_correct (input dirty : List Wire) (modulus : List Bool)
    (q c r t : Wire) (s : BasisState) (hk : input.length = modulus.length)
    (hd : input.length = dirty.length + 1) (hnd : ([q,c,r,t] ++ input ++ dirty).Nodup)
    (hc : s c = false) (hr : s r = false) (ht : s t = false)
    (branch : InstrumentBranch) (hb : branch ∈ (controlledConstMinus input dirty modulus q c r t).run) :
    branch.kraus (ket s) = registerXResetMagnitude branch.history.length •
      ket (constMinusIdealState input modulus q s) := by
  have hg := constMinus_geometry input dirty q c r t hnd
  let flipped : BasisState := fun w => if w ∈ input then s w ^^ s q else s w
  let increment := (List.range input.length).map (Nat.testBit 1)
  let mid := gidneyAddIdealState input increment q flipped
  have hflip (w : Wire) (hw : w ∈ [q,c,r,t]) : flipped w = s w := by
    simp [flipped,hg.2 w hw]
  have hmid := gidneyAddIdealState_correct input increment q flipped (by simp [increment]) hg.1
  obtain ⟨after,ha,hh,htransfer⟩ := gidneyUnitaryBranch (controlledComplement input q) _ branch hb
  have hrest : after.kraus (ket flipped) = registerXResetMagnitude after.history.length •
      ket (constMinusIdealState input modulus q s) := by
    apply horner_seq_branch _ _ flipped mid _ _ _ after ha
    · intro b hb
      have hb' := controlledGidneyAddConst_branch_correct input dirty increment q c r t flipped
        (by simp [increment]) hd hnd ((hflip c (by simp)).trans hc)
        ((hflip r (by simp)).trans hr) ((hflip t (by simp)).trans ht) b hb
      rw [hb'.1,hb'.2]
    · intro b hb
      have clean (w : Wire) (hw : w ∈ [q,c,r,t]) : mid w = s w :=
        (hmid.2 w (hg.2 w hw)).trans (hflip w hw)
      have hb' := controlledGidneyAddConst_branch_correct input dirty modulus q c r t mid
        hk hd hnd ((clean c (by simp)).trans hc) ((clean r (by simp)).trans hr)
        ((clean t (by simp)).trans ht) b hb
      rw [hb'.1,hb'.2]
      rfl
  rw [hh,htransfer]
  rw [Quantum.run_ket_agrees_classical _ _ (by simp [controlledComplement,HPFree])]
  rw [controlledComplement_state input q s hg.1 (hg.2 q (by simp))]
  exact hrest

/-- The actual measured wrapper is well formed on disjoint registers. -/
theorem controlledConstMinus_wellFormed (input dirty : List Wire) (modulus : List Bool)
    (q c r t : Wire) (hk : input.length = modulus.length)
    (hd : input.length = dirty.length + 1) (hnd : ([q,c,r,t] ++ input ++ dirty).Nodup) :
    (controlledConstMinus input dirty modulus q c r t).WellFormed := by
  have hg := constMinus_geometry input dirty q c r t hnd
  refine ⟨?_, AdaptiveCircuit.WellFormed.seq
    (controlledGidneyAddConst_wellFormed input dirty _ q c r t (by simp) hd hnd)
    (controlledGidneyAddConst_wellFormed input dirty modulus q c r t hk hd hnd)⟩
  intro gate hgate
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hgate
  exact fun he => hg.2 q (by simp) (he ▸ hw)

/-- Independent measurement outcomes in two executions still restore the complete
input state, with the product of their positive branch amplitudes. -/
theorem controlledConstMinus_twice (input dirty : List Wire) (modulus : List Bool)
    (q c r t p : Nat) (s : BasisState) (hk : input.length = modulus.length)
    (hd : input.length = dirty.length + 1) (hnd : ([q,c,r,t] ++ input ++ dirty).Nodup)
    (hc : s c = false) (hr : s r = false) (ht : s t = false)
    (hp : p < 2 ^ input.length) (hm : boolWordToNat modulus = p)
    (hx : boolWordToNat (wireValues input s) ≤ p)
    (first second : InstrumentBranch)
    (hfirst : first ∈ (controlledConstMinus input dirty modulus q c r t).run)
    (hsecond : second ∈ (controlledConstMinus input dirty modulus q c r t).run) :
    second.kraus (first.kraus (ket s)) =
      registerXResetMagnitude (first.history.length + second.history.length) • ket s := by
  have hg := constMinus_geometry input dirty q c r t hnd
  have hi := constMinusIdealState_correct input modulus q p s (by omega) hk hg.1
    (hg.2 q (by simp)) hp hm hx
  have hb1 := controlledConstMinus_branch_correct input dirty modulus q c r t s hk hd hnd hc hr ht first hfirst
  have hb2 := controlledConstMinus_branch_correct input dirty modulus q c r t _ hk hd hnd
    ((hi.2 c (hg.2 c (by simp))).trans hc) ((hi.2 r (hg.2 r (by simp))).trans hr)
    ((hi.2 t (hg.2 t (by simp))).trans ht) second hsecond
  rw [hb1,map_smul,hb2,constMinusIdealState_involutive input modulus q p s (by omega)
    hk hg.1 (hg.2 q (by simp)) hp hm hx,smul_smul]
  simp [registerXResetMagnitude,pow_add]

/-- The source EEA negation wrapper on its 515 distinct physical roles. -/
def secp256k1ConstMinus : AdaptiveCircuit :=
  controlledConstMinus (List.range' 4 256) (List.range' 260 255)
    secp256k1ModulusBits 0 1 2 3

private theorem constMinusProduction_layout :
    ([0,1,2,3] ++ List.range' 4 256 ++ List.range' 260 255).Nodup := by
  simp only [List.nodup_append]
  refine ⟨⟨by decide,List.nodup_range',?_⟩,List.nodup_range',?_⟩
  all_goals
    intro a ha b hb he
    simp at ha hb
    omega

set_option maxRecDepth 10000 in
theorem secp256k1ConstMinus_counts :
    gidneyToffoliCount secp256k1ConstMinus = 1528 ∧
    gidneyCnotCount secp256k1ConstMinus = 5305 ∧
    secp256k1ConstMinus.tCount = 10696 ∧
    secp256k1ConstMinus.measurementCount = 510 := by
  have hinc := secp256k1Increment_counts 0 1 2 3
  have hmod := secp256k1ModulusAdd_counts 0 1 2 3
  dsimp only at hinc hmod
  have hseqT (a b : AdaptiveCircuit) : (a.seq b).tCount = a.tCount + b.tCount := by
    simpa only [gidneyGateCount_tCount] using modularGateCount_seq tCost a b
  have hseqCCX (a b : AdaptiveCircuit) : gidneyToffoliCount (a.seq b) =
      gidneyToffoliCount a + gidneyToffoliCount b := modularGateCount_seq _ a b
  have hseqCX (a b : AdaptiveCircuit) : gidneyCnotCount (a.seq b) =
      gidneyCnotCount a + gidneyCnotCount b := modularGateCount_seq _ a b
  have hccx (g : Circuit) (a b : AdaptiveCircuit) :
      gidneyToffoliCount (.unitary g (a.seq b)) =
        (g.map (fun g => match g with | .CCX _ _ _ => 1 | _ => 0)).sum +
          (gidneyToffoliCount a + gidneyToffoliCount b) := by
    exact congrArg (_ + ·) (hseqCCX a b)
  have hcx (g : Circuit) (a b : AdaptiveCircuit) :
      gidneyCnotCount (.unitary g (a.seq b)) =
        (g.map (fun g => match g with | .CX _ _ => 1 | _ => 0)).sum +
          (gidneyCnotCount a + gidneyCnotCount b) := by
    exact congrArg (_ + ·) (hseqCX a b)
  have htc (g : Circuit) (a b : AdaptiveCircuit) :
      (AdaptiveCircuit.unitary g (a.seq b)).tCount = tCount g + (a.tCount + b.tCount) :=
    congrArg (_ + ·) (hseqT a b)
  have hmc (g : Circuit) (a b : AdaptiveCircuit) :
      (AdaptiveCircuit.unitary g (a.seq b)).measurementCount = a.measurementCount + b.measurementCount :=
    modularMeasurements_seq a b
  unfold secp256k1ConstMinus controlledConstMinus
  rw [show (List.range' 4 256).length = 256 from rfl,hccx,hcx,htc,hmc,
    hinc.1,hmod.1,hinc.2.1,hmod.2.1,hinc.2.2.1,hmod.2.2.1,hinc.2.2.2,hmod.2.2.2]
  decide

set_option maxRecDepth 10000 in
theorem secp256k1ConstMinus_wires (w : Wire) :
    w ∈ secp256k1ConstMinus.wires ↔ w ∈ List.range' 0 515 := by
  have hinc := controlledGidneyAddConst_wires 4 260 0 1 2 3
    (List.range' 5 255) (List.range' 261 254) ((List.range' 1 255).map (Nat.testBit 1))
    (by simp) (by simp) w
  have hmod := controlledGidneyAddConst_wires 4 260 0 1 2 3
    (List.range' 5 255) (List.range' 261 254)
    ((List.range' 1 255).map (Nat.testBit (2 ^ 256 - 2 ^ 32 - 977)))
    (by simp) (by simp) w
  have hm : secp256k1ModulusBits = true ::
    (List.range' 1 255).map (Nat.testBit (2 ^ 256 - 2 ^ 32 - 977)) := by decide
  simp only [secp256k1ConstMinus,controlledConstMinus,AdaptiveCircuit.wires,
    modularWires_seq,List.mem_append]
  rw [hm]
  change (w ∈ circuitWires (controlledComplement (List.range' 4 256) 0) ∨
    (w ∈ (controlledGidneyAddConst (4 :: List.range' 5 255) (260 :: List.range' 261 254)
      (true :: (List.range' 1 255).map (Nat.testBit 1)) 0 1 2 3).wires ∨ _)) ↔ _
  rw [hinc]
  rw [show List.range' 4 256 = 4 :: List.range' 5 255 from rfl,
    show List.range' 260 255 = 260 :: List.range' 261 254 from rfl,hmod]
  simp [controlledComplement,circuitWires,gateWires]
  dsimp only [Wire] at *
  constructor
  · intro h
    rcases h with h | h
    · rcases h with h | h | ⟨a,ha,he⟩ <;> omega
    · omega
  · intro h; omega

private theorem constMinusProduction_qubits : secp256k1ConstMinus.qubitCount = 515 := by
  have heq : secp256k1ConstMinus.wires.dedup.toFinset = (List.range' 0 515).toFinset := by
    ext w
    simpa only [List.mem_toFinset,List.mem_dedup] using secp256k1ConstMinus_wires w
  have hc := congrArg Finset.card heq
  simpa only [List.toFinset_card_of_nodup (List.nodup_dedup _),
    List.toFinset_card_of_nodup (List.nodup_range'),List.length_range'] using hc

attribute [local irreducible] controlledConstMinus constMinusIdealState

set_option maxRecDepth 10000 in
/-- Same-circuit canonical arithmetic, branch semantics, normalization and exact
production resources for the EEA preprocessing/postprocessing primitive. -/
theorem secp256k1ConstMinus_correct_resources (s : BasisState)
    (hc : s 1 = false) (hr : s 2 = false) (ht : s 3 = false)
    (hx : boolWordToNat (wireValues (List.range' 4 256) s) ≤ 2 ^ 256 - 2 ^ 32 - 977) :
    let after := constMinusIdealState (List.range' 4 256) secp256k1ModulusBits 0 s
    boolWordToNat (wireValues (List.range' 4 256) after) =
      (if s 0 then 2 ^ 256 - 2 ^ 32 - 977 - boolWordToNat (wireValues (List.range' 4 256) s)
        else boolWordToNat (wireValues (List.range' 4 256) s)) ∧
    (∀ w, w ∉ List.range' 4 256 → after w = s w) ∧
    (∀ branch ∈ secp256k1ConstMinus.run, branch.kraus (ket s) =
      registerXResetMagnitude branch.history.length • ket after) ∧
    (∀ ψ, Instrument.bornMass secp256k1ConstMinus.run ψ = normSq ψ) ∧
    secp256k1ConstMinus.WellFormed ∧
    gidneyToffoliCount secp256k1ConstMinus = 1528 ∧
    gidneyCnotCount secp256k1ConstMinus = 5305 ∧
    secp256k1ConstMinus.tCount = 10696 ∧
    secp256k1ConstMinus.measurementCount = 510 ∧
    secp256k1ConstMinus.qubitCount = 515 := by
  have hw := controlledConstMinus_wellFormed (List.range' 4 256) (List.range' 260 255)
    secp256k1ModulusBits 0 1 2 3 (by simp [secp256k1ModulusBits]) (by simp)
    constMinusProduction_layout
  have hg := constMinus_geometry (List.range' 4 256) (List.range' 260 255) 0 1 2 3
    constMinusProduction_layout
  have hm : boolWordToNat secp256k1ModulusBits = 2 ^ 256 - 2 ^ 32 - 977 :=
    gidneyCompareBits_value 256 _ (by decide)
  have hi := constMinusIdealState_correct (List.range' 4 256) secp256k1ModulusBits 0
    (2 ^ 256 - 2 ^ 32 - 977) s (by simp) (by simp [secp256k1ModulusBits]) hg.1
    (hg.2 0 (by simp)) (by decide) hm hx
  refine ⟨hi.1,hi.2,?_,fun ψ => AdaptiveCircuit.run_preservesBornMass _ hw ψ,hw,
    secp256k1ConstMinus_counts.1,secp256k1ConstMinus_counts.2.1,
    secp256k1ConstMinus_counts.2.2.1,secp256k1ConstMinus_counts.2.2.2,
    constMinusProduction_qubits⟩
  intro b hb
  exact controlledConstMinus_branch_correct (List.range' 4 256) (List.range' 260 255)
    secp256k1ModulusBits 0 1 2 3 s (by simp [secp256k1ModulusBits]) (by simp)
    constMinusProduction_layout hc hr ht b hb

end
end ShorECDLP.Paper2607_13816
