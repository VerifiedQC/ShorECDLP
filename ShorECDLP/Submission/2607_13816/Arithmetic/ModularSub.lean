import ShorECDLP.Submission.«2607_13816».Arithmetic.Doubling

/-!
# Controlled modular subtraction

The source inverse uses a fresh measured addition of the modulus. Its branch
semantics must therefore be established directly, rather than by taking an
adjoint of the measured forward program.
-/
namespace ShorECDLP.Paper2607_13816
open Classical
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-- Source `append_ctrl_sub_modp_quadratic`, with `modulus` encoding `p`. -/
def controlledModularSub (input acc : List Wire) (modulus : List Bool) (p : Nat)
    (q c r t f : Wire) : Quantum.AdaptiveCircuit :=
  .unitary (controlledCompareLT acc input q c f)
    ((controlledGidneyAddConst acc (input.take (acc.length - 1)) modulus f c r t).seq
      ((gidneyCompareGE acc input p c r t f).seq
        (.unitary (controlledSubCarry input acc q c f) .done)))

/-- All four inverse stages respect the same reusable physical layout. -/
theorem controlledModularSub_wellFormed (input acc : List Wire) (modulus : List Bool) (p : Nat)
    (q c r t f : Wire) (hlen : input.length = acc.length) (hne : 0 < acc.length)
    (hm : acc.length = modulus.length) (hnd : ([q,c,r,t,f] ++ input ++ acc).Nodup) :
    (controlledModularSub input acc modulus p q c r t f).WellFormed := by
  have hl := modularAdd_layout input acc q c r t f hnd
  have hd : acc.length = (input.take (acc.length - 1)).length + 1 := by
    rw [List.length_take,hlen,Nat.min_eq_left (Nat.sub_le _ _)]
    omega
  exact ⟨controlledCompareLT_wellFormed acc input q c f hlen.symm hl.2.2.2,
    Quantum.AdaptiveCircuit.WellFormed.seq
      (controlledGidneyAddConst_wellFormed acc _ modulus f c r t hm hd hl.2.2.1)
      (Quantum.AdaptiveCircuit.WellFormed.seq
        (gidneyCompareGE_wellFormed acc input p c r t f hlen.symm hl.2.1)
        ⟨(circuitWellFormed_adjoint _).mpr
          (controlledAddCarry_wellFormed input acc q c f hlen hl.1),trivial⟩)⟩

/-- Deterministic basis action of the four source subtraction stages. -/
def modularSubIdealState (input acc : List Wire) (modulus : List Bool) (p : Nat)
    (q c f : Wire) (s : BasisState) : BasisState :=
  let corrected := gidneyAddIdealState acc modulus f
    (run (controlledCompareLT acc input q c f) s)
  run (controlledSubCarry input acc q c f)
    (upd corrected f (Bool.xor (corrected f)
      (decide (p ≤ boolWordToNat (wireValues acc corrected)))))

/-- Every branch of the actual inverse stages has the same positive basis action.
No canonical-value assumption is needed for this operational stage theorem. -/
theorem controlledModularSub_branch_correct (input acc : List Wire) (modulus : List Bool)
    (p : Nat) (q c r t f : Wire) (s : BasisState)
    (hlen : input.length = acc.length) (hne : 0 < acc.length)
    (hm : acc.length = modulus.length) (hnd : ([q,c,r,t,f] ++ input ++ acc).Nodup)
    (hc : s c = false) (hr : s r = false) (ht : s t = false)
    (branch : Quantum.InstrumentBranch)
    (hb : branch ∈ (controlledModularSub input acc modulus p q c r t f).run) :
    let m := (if modulus.all (fun k => !k) then 0 else (input.take (acc.length - 1)).length) +
      (if p = 0 ∨ 2 ^ acc.length ≤ p then 0 else acc.length)
    branch.history.length = m ∧ branch.kraus (Quantum.ket s) =
      Quantum.registerXResetMagnitude m • Quantum.ket (modularSubIdealState input acc modulus p q c f s) := by
  have hl := modularAdd_layout input acc q c r t f hnd
  have hd : acc.length = (input.take (acc.length - 1)).length + 1 := by
    rw [List.length_take,hlen,Nat.min_eq_left (Nat.sub_le _ _)]
    omega
  have hfnd := (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp hl.2.2.2).2).2).2
  have hsep := (List.nodup_append.mp hnd).2.2
  have hw (w : Wire) (h : w ∈ [c,r,t]) : w ≠ f ∧ w ∉ acc := by
    have hsc := (List.nodup_append.mp (List.nodup_append.mp hnd).1).1
    have hlist : ([c,r,t] ++ [f]).Nodup := (List.nodup_cons.mp hsc).2
    have hne := (List.nodup_append.mp hlist).2.2
    refine ⟨fun he => hne w h f (by simp) he,?_⟩
    intro ha
    exact hsep w (by simp only [List.mem_append,List.mem_cons,List.not_mem_nil] at h ⊢; tauto) w ha rfl
  let compared := run (controlledCompareLT acc input q c f) s
  let corrected := gidneyAddIdealState acc modulus f compared
  have hcmpframe (w : Wire) (h : w ∈ [c,r,t]) : compared w = s w := by
    dsimp only [compared]
    rw [controlledCompareLT_correct acc input q c f s hlen.symm hl.2.2.2 hc]
    simp [upd,(hw w h).1]
  have haddframe := (gidneyAddIdealState_correct acc modulus f compared hm
    (List.nodup_append.mp hfnd).1).2
  have hcorrected (w : Wire) (h : w ∈ [c,r,t]) : corrected w = s w :=
    (haddframe w (hw w h).2).trans (hcmpframe w h)
  obtain ⟨after,ha,hh,htransfer⟩ := gidneyUnitaryBranch (controlledCompareLT acc input q c f) _ branch hb
  simp only [Quantum.AdaptiveCircuit.run_seq,Quantum.Instrument.seq,List.mem_flatMap,List.mem_map,
    Quantum.AdaptiveCircuit.run_unitary_done,List.mem_singleton] at ha
  obtain ⟨addBranch,haddBranch,compareTail,hcompareTail,rfl⟩ := ha
  obtain ⟨compareBranch,hcompare,last,rfl,rfl⟩ := hcompareTail
  have hadd := controlledGidneyAddConst_branch_correct acc (input.take (acc.length - 1)) modulus f c r t
    compared hm hd hl.2.2.1
    ((hcmpframe c (by simp)).trans hc) ((hcmpframe r (by simp)).trans hr)
    ((hcmpframe t (by simp)).trans ht) addBranch haddBranch
  have hcmp := gidneyCompareGE_branch_correct acc input p c r t f corrected hlen.symm hl.2.1
    ((hcorrected c (by simp)).trans hc) ((hcorrected r (by simp)).trans hr)
    ((hcorrected t (by simp)).trans ht) compareBranch hcompare
  dsimp only at hadd hcmp ⊢
  constructor
  · rw [hh]
    simp only [Quantum.InstrumentBranch.seq,List.length_append,List.length_nil,Nat.add_zero,hadd.1,hcmp.1]
  · rw [htransfer]
    simp only [Quantum.InstrumentBranch.seq,LinearMap.comp_apply]
    rw [Quantum.run_ket_agrees_classical _ _ (controlledCompareLT_HPFree acc input q c f)]
    change Quantum.run (controlledSubCarry input acc q c f)
      (compareBranch.kraus (addBranch.kraus (Quantum.ket compared))) = _
    rw [hadd.2,map_smul]
    change Quantum.run (controlledSubCarry input acc q c f)
      (Quantum.registerXResetMagnitude _ • compareBranch.kraus (Quantum.ket corrected)) = _
    rw [hcmp.2,map_smul,map_smul]
    have hfree : HPFree (controlledSubCarry input acc q c f) := by
      exact controlledSubCarry_HPFree input acc q c f
    rw [Quantum.run_ket_agrees_classical _ _ hfree]
    simp only [smul_smul,Quantum.registerXResetMagnitude,← pow_add]
    rfl

/-- Subtraction reverses addition on the complete state for canonical operands. -/
theorem modularSubIdealState_after_add (input acc : List Wire)
    (correction modulus : List Bool) (p : Nat) (q c r t f : Wire) (s : BasisState)
    (hlen : input.length = acc.length) (hk : acc.length = correction.length)
    (hm : acc.length = modulus.length) (hnd : ([q,c,r,t,f] ++ input ++ acc).Nodup)
    (hc : s c = false) (hf : s f = false) (hp : p < 2 ^ acc.length)
    (hx : boolWordToNat (wireValues input s) < p)
    (hy : boolWordToNat (wireValues acc s) < p)
    (hconstant : boolWordToNat correction = 2 ^ acc.length - p)
    (hmodulus : boolWordToNat modulus = p) :
    modularSubIdealState input acc modulus p q c f
      (modularAddIdealState input acc correction p q c f s) = s := by
  have hl := modularAdd_layout input acc q c r t f hnd
  have hfacc : f ∉ acc := by
    have hshort := hl.2.2.2
    have hn := (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp hshort).2).2).1
    exact fun h => hn (List.mem_append_left _ h)
  unfold modularSubIdealState
  rw [modularAddIdealState_uncorrect input acc correction modulus p q c r t f s
    hlen hk hm hnd hc hf hp hx hy hconstant hmodulus]
  let low := run (controlledAddCarry input acc q c f) s
  have hword (b : Bool) : wireValues acc (upd low f b) = wireValues acc low := by
    apply List.map_congr_left
    intro w hw
    have hn : w ≠ f := by intro he; subst w; exact hfacc hw
    simp [upd,hn]
  let flagged := upd low f (Bool.xor (low f)
    (decide (p ≤ boolWordToNat (wireValues acc low))))
  have hcancel : upd flagged f (Bool.xor (flagged f)
      (decide (p ≤ boolWordToNat (wireValues acc flagged)))) = low := by
    dsimp only [flagged]
    rw [hword]
    funext w
    by_cases hw : w = f <;> simp [upd,hw,Bool.xor_assoc]
  change run (controlledSubCarry input acc q c f) _ = s
  rw [hcancel]
  exact controlledSubCarry_after_add input acc q c f s hlen hl.1

/-- Concrete 256-bit inverse correction on the forward modular-adder layout. -/
def secp256k1ModularSub : Quantum.AdaptiveCircuit :=
  controlledModularSub (List.range' 260 256) (List.range' 4 256) secp256k1ModulusBits
    (2 ^ 256 - (2 ^ 32 + 977)) 516 1 2 3 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem subProduction_layout :
    ([516,1,2,3,0] ++ List.range' 260 256 ++ List.range' 4 256).Nodup := by decide

private theorem subProduction_decompose : secp256k1ModularSub =
    .unitary (controlledCompareLT (List.range' 4 256) (List.range' 260 256) 516 1 0)
      ((controlledGidneyAddConst (List.range' 4 256) (List.range' 260 255)
        secp256k1ModulusBits 0 1 2 3).seq
        ((gidneyCompareGE (List.range' 4 256) (List.range' 260 256)
          (2 ^ 256 - (2 ^ 32 + 977)) 1 2 3 0).seq
          (.unitary (controlledSubCarry (List.range' 260 256) (List.range' 4 256) 516 1 0) .done))) := rfl

set_option maxRecDepth 100000 in
/-- Production inverse-addition costs for arbitrary scalar labels. -/
theorem secp256k1ModularSub_counts (q c r t f : Wire) :
    let ac := controlledModularSub (List.range' 260 256) (List.range' 4 256) secp256k1ModulusBits
      (2 ^ 256 - (2 ^ 32 + 977)) q c r t f
    gidneyToffoliCount ac = 2813 ∧ gidneyCnotCount ac = 7350 ∧
      ac.tCount = 19691 ∧ ac.measurementCount = 511 := by
  have hl := controlledCompareLT_counts 4 (List.range' 5 255) (List.range' 260 256) q c f (by simp)
  have ha := secp256k1ModulusAdd_counts f c r t
  have hg := secp256k1ModularCompare_counts c r t f
  have hst := controlledAddCarry_toffoliCount (List.range' 260 256) (List.range' 4 256) q c f (by simp)
  have hsc := controlledAddCarry_cnotCount (List.range' 260 256) (List.range' 4 256) q c f (by simp)
  have hstt := controlledAddCarry_tCount (List.range' 260 256) (List.range' 4 256) q c f (by simp)
  have h := doublingFour_counts
    (controlledCompareLT (List.range' 4 256) (List.range' 260 256) q c f)
    (controlledSubCarry (List.range' 260 256) (List.range' 4 256) q c f)
    (controlledGidneyAddConst (List.range' 4 256) (List.range' 260 255) secp256k1ModulusBits f c r t)
    (gidneyCompareGE (List.range' 4 256) (List.range' 260 256) (2 ^ 256 - (2 ^ 32 + 977)) c r t f)
  change eeaToffoliCount (controlledCompareLT (List.range' 4 256) _ q c f) = 513 ∧
    eeaCnotCount (controlledCompareLT (List.range' 4 256) _ q c f) = 1024 ∧
    eeaXCount (controlledCompareLT (List.range' 4 256) _ q c f) = 516 ∧
    tCount (controlledCompareLT (List.range' 4 256) _ q c f) = 3591 at hl
  dsimp only at ha hg ⊢
  unfold controlledModularSub
  rw [show (List.range' 4 256).length - 1 = 255 from rfl,
    show (List.range' 260 256).take 255 = List.range' 260 255 from rfl]
  rcases h with ⟨htf,hcx,ht,hm⟩
  rw [htf,hcx,ht,hm,hl.1,hl.2.1,hl.2.2.2,ha.1,ha.2.1,ha.2.2.1,ha.2.2.2,
    hg.1,hg.2.1,hg.2.2.1,hg.2.2.2,controlledSubCarry,
    eeaToffoliCount_adjoint,eeaCnotCount_adjoint,tCount_adjoint,hst,hsc,hstt]
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem subProduction_wires (w : Wire) :
    w ∈ secp256k1ModularSub.wires ↔ w ∈ List.range' 0 517 := by
  have ha := controlledGidneyAddConst_wires 4 260 0 1 2 3 (List.range' 5 255) (List.range' 261 254)
    ((List.range' 1 255).map (Nat.testBit (2 ^ 256 - 2 ^ 32 - 977))) (by simp) (by simp) w
  have hb : secp256k1ModulusBits = true ::
    (List.range' 1 255).map (Nat.testBit (2 ^ 256 - 2 ^ 32 - 977)) := by decide
  have ha' : w ∈ (controlledGidneyAddConst (List.range' 4 256) (List.range' 260 255)
      secp256k1ModulusBits 0 1 2 3).wires ↔
      w ∈ [0,1,2,3] ++ List.range' 4 256 ++ List.range' 260 255 := by
    rw [hb]; exact ha
  have hl := controlledCompareLT_wires 4 (List.range' 5 255) (List.range' 260 256) 516 1 0 w (by simp)
  have hs := (controlledAddCarry_usesOnly (List.range' 260 256) (List.range' 4 256) 516 1 0).adjoint
  rw [subProduction_decompose]
  simp only [Quantum.AdaptiveCircuit.wires,List.mem_append,modularWires_seq,
    secp256k1ModularCompare_wires,ha',List.not_mem_nil,or_false]
  change (w ∈ circuitWires (controlledCompareLT (4 :: List.range' 5 255) _ 516 1 0) ∨ _ ∨ _ ∨ _) ↔ _
  rw [hl]
  constructor
  · intro h
    rcases h with h | h | h | h
    · simp at h ⊢; dsimp only [Wire] at *; omega
    · simp at h ⊢; dsimp only [Wire] at *; omega
    · simp at h ⊢; dsimp only [Wire] at *; omega
    · obtain ⟨g,hg,hw⟩ := List.mem_flatMap.mp h
      have hh := hs g hg w hw
      simp at hh ⊢; dsimp only [Wire] at *; omega
  · intro h
    simp at h
    by_cases hw : w = 516
    · left; simp [hw]
    · right; right; left; simp; dsimp only [Wire] at *; omega

private theorem subProduction_qubits : secp256k1ModularSub.qubitCount = 517 := by
  have heq : secp256k1ModularSub.wires.dedup.toFinset = (List.range' 0 517).toFinset := by
    ext w; simpa only [List.mem_toFinset,List.mem_dedup] using subProduction_wires w
  have hc := congrArg Finset.card heq
  simpa only [List.toFinset_card_of_nodup (List.nodup_dedup _),
    List.toFinset_card_of_nodup (List.nodup_range'),List.length_range'] using hc

attribute [local irreducible] controlledModularSub modularSubIdealState

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The same source inverse circuit restores a canonical pre-addition state in every
measurement branch, with normalized mass and explicit gate and physical-wire counts. -/
theorem secp256k1ModularSub_after_add_correct_resources (s : BasisState)
    (hc : s 1 = false) (hr : s 2 = false) (ht : s 3 = false) (hf : s 0 = false)
    (hx : boolWordToNat (wireValues (List.range' 260 256) s) < 2 ^ 256 - (2 ^ 32 + 977))
    (hy : boolWordToNat (wireValues (List.range' 4 256) s) < 2 ^ 256 - (2 ^ 32 + 977)) :
    let after := modularAddIdealState (List.range' 260 256) (List.range' 4 256)
      secp256k1ReductionConstantBits (2 ^ 256 - (2 ^ 32 + 977)) 516 1 0 s
    (∀ branch ∈ secp256k1ModularSub.run, branch.history.length = 511 ∧
      branch.kraus (Quantum.ket after) = Quantum.registerXResetMagnitude 511 • Quantum.ket s) ∧
    Quantum.Instrument.bornMass secp256k1ModularSub.run (Quantum.ket after) = 1 ∧
    secp256k1ModularSub.WellFormed ∧ gidneyToffoliCount secp256k1ModularSub = 2813 ∧
    gidneyCnotCount secp256k1ModularSub = 7350 ∧ secp256k1ModularSub.tCount = 19691 ∧
    secp256k1ModularSub.measurementCount = 511 ∧ secp256k1ModularSub.qubitCount = 517 := by
  have hlen : (List.range' 260 256).length = (List.range' 4 256).length := by simp
  have hne : 0 < (List.range' 4 256).length := by simp
  have hk : (List.range' 4 256).length = secp256k1ReductionConstantBits.length := by simp [secp256k1ReductionConstantBits]
  have hm : (List.range' 4 256).length = secp256k1ModulusBits.length := by simp [secp256k1ModulusBits]
  have hp : 2 ^ 256 - (2 ^ 32 + 977) < 2 ^ (List.range' 4 256).length := by decide
  have hv : boolWordToNat secp256k1ReductionConstantBits =
      2 ^ (List.range' 4 256).length - (2 ^ 256 - (2 ^ 32 + 977)) := by
    rw [secp256k1ReductionConstant_value]; decide
  have hmod : boolWordToNat secp256k1ModulusBits = 2 ^ 256 - (2 ^ 32 + 977) := by decide
  have hw : secp256k1ModularSub.WellFormed := controlledModularSub_wellFormed _ _ _ _
    516 1 2 3 0 hlen hne hm subProduction_layout
  have ha := modularAddIdealState_correct _ _ _ _ 516 1 2 3 0 s hlen hk subProduction_layout hc hf hp hx hy hv
  have hundo := modularSubIdealState_after_add _ _ _ _ _ 516 1 2 3 0 s
    hlen hk hm subProduction_layout hc hf hp hx hy hv hmod
  dsimp only
  refine ⟨?_,Quantum.AdaptiveCircuit.run_bornMass_eq_one _ hw _ (Quantum.normSq_ket _),hw,
    (secp256k1ModularSub_counts 516 1 2 3 0).1,(secp256k1ModularSub_counts 516 1 2 3 0).2.1,(secp256k1ModularSub_counts 516 1 2 3 0).2.2.1,
    (secp256k1ModularSub_counts 516 1 2 3 0).2.2.2,subProduction_qubits⟩
  intro branch hb
  have h := controlledModularSub_branch_correct _ _ _ _ 516 1 2 3 0 _ hlen hne hm subProduction_layout
    ((ha.2 1 (by simp)).trans hc) ((ha.2 2 (by simp)).trans hr) ((ha.2 3 (by simp)).trans ht) branch hb
  have hz : secp256k1ModulusBits.all (fun k => !k) = false := by decide
  have hshort : ¬ (2 ^ 256 - (2 ^ 32 + 977) = 0 ∨
      2 ^ (List.range' 4 256).length ≤ 2 ^ 256 - (2 ^ 32 + 977)) := by decide
  simpa only [hundo,hz,Bool.false_eq_true,if_false,if_neg hshort,List.length_take,List.length_range'] using h

end ShorECDLP.Paper2607_13816
