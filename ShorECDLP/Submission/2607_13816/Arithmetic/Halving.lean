import ShorECDLP.Submission.«2607_13816».Arithmetic.ModularSub

/-!
# Measured modular halving

The source clears the low-bit reduction flag with a fresh modulus addition and
comparison, then reverses the unitary shift. Only that final unitary block is
adjointed; the measured stages are proved directly.
-/
namespace ShorECDLP.Paper2607_13816
open Classical
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-- Source `append_halve_modp_quadratic`. The reverse shift consists of a flag-to-low
CNOT, the ascending adjacent swaps, and the high-to-flag CNOT. -/
def modularHalve (acc dirty : List Wire) (modulus : List Bool) (p : Nat)
    (c r t f : Wire) : Quantum.AdaptiveCircuit :=
  match acc with
  | [] => .done
  | a :: rest => .unitary [.CX a f]
      ((controlledGidneyAddConst (a :: rest) (dirty.take rest.length) modulus f c r t).seq
        ((gidneyCompareGE (a :: rest) dirty p c r t f).seq
          (.unitary (doublingShift (a :: rest) f).adjoint .done)))

/-- Basis action of the actual source halving stages. -/
def modularHalveIdealState (acc : List Wire) (modulus : List Bool) (p : Nat)
    (f : Wire) (s : BasisState) : BasisState :=
  match acc with
  | [] => s
  | a :: rest =>
      let corrected := gidneyAddIdealState (a :: rest) modulus f (run [.CX a f] s)
      run (doublingShift (a :: rest) f).adjoint
        (upd corrected f (Bool.xor (corrected f)
          (decide (p ≤ boolWordToNat (wireValues (a :: rest) corrected)))))

/-- Halving restores the complete state after doubling a canonical residue modulo
an odd modulus. The clean flag is restored along with the data word. -/
theorem modularHalveIdealState_after_double (a f : Wire) (rest : List Wire)
    (correction modulus : List Bool) (p : Nat) (s : BasisState)
    (hnd : (f :: a :: rest).Nodup) (hf : s f = false)
    (hk : (a :: rest).length = correction.length) (hm : (a :: rest).length = modulus.length)
    (hp : p < 2 ^ (a :: rest).length)
    (hx : boolWordToNat (wireValues (a :: rest) s) < p) (hodd : p % 2 = 1)
    (hconstant : boolWordToNat correction = 2 ^ (a :: rest).length - p)
    (hmodulus : boolWordToNat modulus = p) :
    modularHalveIdealState (a :: rest) modulus p f
      (modularDoubleIdealState (a :: rest) correction p f s) = s := by
  simp only [modularHalveIdealState]
  rw [modularDoubleIdealState_uncorrect a f rest correction modulus p s
    hnd hf hk hm hp hx hodd hconstant hmodulus]
  let low := run (doublingShift (a :: rest) f) s
  have hword (b : Bool) : wireValues (a :: rest) (upd low f b) = wireValues (a :: rest) low := by
    apply List.map_congr_left
    intro w hw
    have hn : w ≠ f := by intro he; subst w; exact (List.nodup_cons.mp hnd).1 hw
    simp [upd,hn]
  let flagged := upd low f (Bool.xor (low f)
    (decide (p ≤ boolWordToNat (wireValues (a :: rest) low))))
  have hcancel : upd flagged f (Bool.xor (flagged f)
      (decide (p ≤ boolWordToNat (wireValues (a :: rest) flagged)))) = low := by
    dsimp only [flagged]
    rw [hword]
    funext w
    by_cases hw : w = f <;> simp [upd,hw,Bool.xor_assoc]
  change run (doublingShift (a :: rest) f).adjoint _ = s
  rw [hcancel]
  exact run_adjoint_run_classical _ (doublingShift_wellFormed a f rest hnd) s

/-- The measured inverse uses the same reusable register layout as doubling. -/
theorem modularHalve_wellFormed (a : Wire) (rest dirty : List Wire) (modulus : List Bool)
    (p : Nat) (c r t f : Wire) (hm : (a :: rest).length = modulus.length)
    (hd : (a :: rest).length = dirty.length) (hnd : ([c,r,t,f] ++ (a :: rest) ++ dirty).Nodup) :
    (modularHalve (a :: rest) dirty modulus p c r t f).WellFormed := by
  have hl := doubling_layout (a :: rest) dirty c r t f hnd
  have hfa : f ≠ a := by intro he; exact (List.nodup_cons.mp hl.1).1 (by simp [he])
  have hshort : ([f,c,r,t] ++ (a :: rest) ++ dirty.take rest.length).Nodup :=
    List.Nodup.sublist ((List.Sublist.refl ([f,c,r,t] ++ (a :: rest))).append (List.take_sublist _ _)) hl.2
  have hlen : (a :: rest).length = (dirty.take rest.length).length + 1 := by
    simp only [List.length_take,List.length_cons]
    rw [Nat.min_eq_left (by simp only [List.length_cons] at hd; omega : rest.length ≤ dirty.length)]
  exact ⟨by simp [CircuitWellFormed,Gate.WellFormed,Ne.symm hfa],
    Quantum.AdaptiveCircuit.WellFormed.seq
      (controlledGidneyAddConst_wellFormed _ _ _ f c r t hm hlen hshort)
      (Quantum.AdaptiveCircuit.WellFormed.seq
        (gidneyCompareGE_wellFormed _ dirty p c r t f hd hnd)
        ⟨(circuitWellFormed_adjoint _).mpr (doublingShift_wellFormed a f rest hl.1),trivial⟩)⟩

private theorem halvingShift_HPFree (acc : List Wire) (f : Wire) :
    HPFree (doublingShift acc f).adjoint := by
  have h := doublingShift_HPFree acc f
  generalize doublingShift acc f = circuit at *
  induction circuit with
  | nil => simp
  | cons g circuit ih =>
    have hp := (hpFree_cons g circuit).mp h
    rw [circuit_adjoint_cons,hpFree_append]
    refine ⟨ih hp.2,?_⟩
    cases g <;> simp_all [Gate.adjoint]

/-- Each measurement branch implements the same halving stage action with a positive,
input-independent coefficient and restoration of all borrowed workspace. -/
theorem modularHalve_branch_correct (a : Wire) (rest dirty : List Wire) (modulus : List Bool)
    (p : Nat) (c r t f : Wire) (s : BasisState)
    (hm : (a :: rest).length = modulus.length) (hd : (a :: rest).length = dirty.length)
    (hnd : ([c,r,t,f] ++ (a :: rest) ++ dirty).Nodup)
    (hc : s c = false) (hr : s r = false) (ht : s t = false)
    (branch : Quantum.InstrumentBranch)
    (hb : branch ∈ (modularHalve (a :: rest) dirty modulus p c r t f).run) :
    let m := (if modulus.all (fun k => !k) then 0 else (dirty.take rest.length).length) +
      (if p = 0 ∨ 2 ^ (a :: rest).length ≤ p then 0 else (a :: rest).length)
    branch.history.length = m ∧ branch.kraus (Quantum.ket s) =
      Quantum.registerXResetMagnitude m • Quantum.ket (modularHalveIdealState (a :: rest) modulus p f s) := by
  have hl := doubling_layout (a :: rest) dirty c r t f hnd
  have hshort : ([f,c,r,t] ++ (a :: rest) ++ dirty.take rest.length).Nodup :=
    List.Nodup.sublist ((List.Sublist.refl ([f,c,r,t] ++ (a :: rest))).append (List.take_sublist _ _)) hl.2
  have hlen : (a :: rest).length = (dirty.take rest.length).length + 1 := by
    simp only [List.length_take,List.length_cons]
    rw [Nat.min_eq_left (by simp only [List.length_cons] at hd; omega : rest.length ≤ dirty.length)]
  have hpfx := (List.nodup_append.mp hnd).1
  have hsc := (List.nodup_append.mp hpfx).1
  have hsep := (List.nodup_append.mp hpfx).2.2
  have hw (w : Wire) (h : w ∈ [c,r,t]) : w ≠ f ∧ w ∉ a :: rest := by
    have hdis := (List.nodup_append.mp (show ([c,r,t] ++ [f]).Nodup from hsc)).2.2
    refine ⟨fun he => hdis w h f (by simp) he,?_⟩
    intro ha
    exact hsep w (by simp only [List.mem_cons,List.not_mem_nil] at h ⊢; tauto) w ha rfl
  let compared := run ([.CX a f] : Circuit) s
  let corrected := gidneyAddIdealState (a :: rest) modulus f compared
  have hfirst (w : Wire) (h : w ∈ [c,r,t]) : compared w = s w := by
    simp [compared,run,applyGate,upd,(hw w h).1]
  have haddframe := (gidneyAddIdealState_correct (a :: rest) modulus f compared hm
    (List.nodup_cons.mp hl.1).2).2
  have hcorrected (w : Wire) (h : w ∈ [c,r,t]) : corrected w = s w :=
    (haddframe w (hw w h).2).trans (hfirst w h)
  obtain ⟨after,ha,hh,htransfer⟩ := gidneyUnitaryBranch ([.CX a f] : Circuit) _ branch hb
  simp only [Quantum.AdaptiveCircuit.run_seq,Quantum.Instrument.seq,List.mem_flatMap,List.mem_map,
    Quantum.AdaptiveCircuit.run_unitary_done,List.mem_singleton] at ha
  obtain ⟨addBranch,haddBranch,compareTail,hcompareTail,rfl⟩ := ha
  obtain ⟨compareBranch,hcompare,last,rfl,rfl⟩ := hcompareTail
  have hadd := controlledGidneyAddConst_branch_correct (a :: rest) (dirty.take rest.length) modulus f c r t
    compared hm hlen hshort ((hfirst c (by simp)).trans hc) ((hfirst r (by simp)).trans hr)
    ((hfirst t (by simp)).trans ht) addBranch haddBranch
  have hcmp := gidneyCompareGE_branch_correct (a :: rest) dirty p c r t f corrected hd hnd
    ((hcorrected c (by simp)).trans hc) ((hcorrected r (by simp)).trans hr)
    ((hcorrected t (by simp)).trans ht) compareBranch hcompare
  dsimp only at hadd hcmp ⊢
  constructor
  · rw [hh]
    simp only [Quantum.InstrumentBranch.seq,List.length_append,List.length_nil,Nat.add_zero,hadd.1,hcmp.1]
  · rw [htransfer]
    simp only [Quantum.InstrumentBranch.seq,LinearMap.comp_apply]
    rw [Quantum.run_ket_agrees_classical _ _ (by simp : HPFree ([.CX a f] : Circuit))]
    change Quantum.run (doublingShift (a :: rest) f).adjoint
      (compareBranch.kraus (addBranch.kraus (Quantum.ket compared))) = _
    rw [hadd.2,map_smul]
    change Quantum.run (doublingShift (a :: rest) f).adjoint
      (Quantum.registerXResetMagnitude _ • compareBranch.kraus (Quantum.ket corrected)) = _
    rw [hcmp.2,map_smul,map_smul,Quantum.run_ket_agrees_classical _ _ (halvingShift_HPFree (a :: rest) f)]
    simp only [smul_smul,Quantum.registerXResetMagnitude,← pow_add]
    rfl

/-- Concrete secp256k1 halving on 256 data bits, 256 borrowed bits and four clean work bits. -/
def secp256k1ModularHalve : Quantum.AdaptiveCircuit :=
  modularHalve (List.range' 4 256) (List.range' 260 256) secp256k1ModulusBits
    (2 ^ 256 - (2 ^ 32 + 977)) 1 2 3 0

private theorem halveProduction_layout :
    ([1,2,3,0] ++ List.range' 4 256 ++ List.range' 260 256).Nodup := by
  simp only [List.nodup_append]
  refine ⟨⟨by decide,List.nodup_range',?_⟩,List.nodup_range',?_⟩
  all_goals
    intro a ha b hb he
    simp at ha hb
    omega

private theorem halveProduction_decompose : secp256k1ModularHalve =
    .unitary [.CX 4 0]
      ((controlledGidneyAddConst (List.range' 4 256) (List.range' 260 255)
        secp256k1ModulusBits 0 1 2 3).seq
        ((gidneyCompareGE (List.range' 4 256) (List.range' 260 256)
          (2 ^ 256 - (2 ^ 32 + 977)) 1 2 3 0).seq
          (.unitary (doublingShift (List.range' 4 256) 0).adjoint .done))) := rfl

private theorem halveProduction_counts :
    gidneyToffoliCount secp256k1ModularHalve = 1531 ∧
    gidneyCnotCount secp256k1ModularHalve = 6070 ∧
    secp256k1ModularHalve.tCount = 10717 ∧ secp256k1ModularHalve.measurementCount = 511 := by
  have ha := secp256k1ModulusAdd_counts 0 1 2 3
  have hg := secp256k1ModularCompare_counts 1 2 3 0
  have hs := doublingShift_counts 4 0 (List.range' 5 255)
  change eeaToffoliCount (doublingShift (List.range' 4 256) 0) = 0 ∧
    eeaCnotCount (doublingShift (List.range' 4 256) 0) = 767 ∧
    tCount (doublingShift (List.range' 4 256) 0) = 0 at hs
  rw [halveProduction_decompose]
  have h := doublingFour_counts ([.CX 4 0] : Circuit) (doublingShift (List.range' 4 256) 0).adjoint
    (controlledGidneyAddConst (List.range' 4 256) (List.range' 260 255) secp256k1ModulusBits 0 1 2 3)
    (gidneyCompareGE (List.range' 4 256) (List.range' 260 256) (2 ^ 256 - (2 ^ 32 + 977)) 1 2 3 0)
  dsimp only at ha hg
  rcases h with ⟨htf,hcx,ht,hm⟩
  rw [htf,hcx,ht,hm,eeaToffoliCount_adjoint,eeaCnotCount_adjoint,tCount_adjoint,
    ha.1,ha.2.1,ha.2.2.1,ha.2.2.2,hg.1,hg.2.1,hg.2.2.1,hg.2.2.2,hs.1,hs.2.1,hs.2.2]
  decide

private theorem halveProduction_wires (w : Wire) :
    w ∈ secp256k1ModularHalve.wires ↔ w ∈ List.range' 0 516 := by
  have ha := controlledGidneyAddConst_wires 4 260 0 1 2 3 (List.range' 5 255) (List.range' 261 254)
    ((List.range' 1 255).map (Nat.testBit (2 ^ 256 - 2 ^ 32 - 977))) (by simp) (by simp) w
  have hb : secp256k1ModulusBits = true ::
    (List.range' 1 255).map (Nat.testBit (2 ^ 256 - 2 ^ 32 - 977)) := by decide
  have ha' : w ∈ (controlledGidneyAddConst (List.range' 4 256) (List.range' 260 255)
      secp256k1ModulusBits 0 1 2 3).wires ↔
      w ∈ [0,1,2,3] ++ List.range' 4 256 ++ List.range' 260 255 := by
    rw [hb]; exact ha
  have hs := (doublingShift_usesOnly 4 0 (List.range' 5 255)).adjoint
  rw [halveProduction_decompose]
  simp only [Quantum.AdaptiveCircuit.wires,List.mem_append,modularWires_seq,
    secp256k1ModularCompare_wires,ha',List.not_mem_nil,or_false]
  constructor
  · intro h
    rcases h with h | h | h | h
    · simp [circuitWires,gateWires] at h
      rcases h with rfl | rfl <;> simp
    · simp at h ⊢; dsimp only [Wire] at *; omega
    · simp at h ⊢; dsimp only [Wire] at *; omega
    · obtain ⟨g,hg,hw⟩ := List.mem_flatMap.mp h
      have hh := hs g hg w hw
      simp at hh ⊢; dsimp only [Wire] at *; omega
  · intro h
    right; right; left
    simp at h ⊢; dsimp only [Wire] at *; omega

private theorem halveProduction_qubits : secp256k1ModularHalve.qubitCount = 516 := by
  have heq : secp256k1ModularHalve.wires.dedup.toFinset = (List.range' 0 516).toFinset := by
    ext w; simpa only [List.mem_toFinset,List.mem_dedup] using halveProduction_wires w
  have hc := congrArg Finset.card heq
  simpa only [List.toFinset_card_of_nodup (List.nodup_dedup _),
    List.toFinset_card_of_nodup (List.nodup_range'),List.length_range'] using hc

attribute [local irreducible] modularHalve modularHalveIdealState

set_option maxHeartbeats 4000000 in
/-- The actual 256-bit inverse restores a canonical pre-doubling state in every
branch; the same circuit has normalized mass and the listed exact resources. -/
theorem secp256k1ModularHalve_after_double_correct_resources (s : BasisState)
    (hc : s 1 = false) (hr : s 2 = false) (ht : s 3 = false) (hf : s 0 = false)
    (hx : boolWordToNat (wireValues (List.range' 4 256) s) < 2 ^ 256 - (2 ^ 32 + 977)) :
    let after := modularDoubleIdealState (List.range' 4 256)
      secp256k1ReductionConstantBits (2 ^ 256 - (2 ^ 32 + 977)) 0 s
    (∀ branch ∈ secp256k1ModularHalve.run, branch.history.length = 511 ∧
      branch.kraus (Quantum.ket after) = Quantum.registerXResetMagnitude 511 • Quantum.ket s) ∧
    Quantum.Instrument.bornMass secp256k1ModularHalve.run (Quantum.ket after) = 1 ∧
    secp256k1ModularHalve.WellFormed ∧ gidneyToffoliCount secp256k1ModularHalve = 1531 ∧
    gidneyCnotCount secp256k1ModularHalve = 6070 ∧ secp256k1ModularHalve.tCount = 10717 ∧
    secp256k1ModularHalve.measurementCount = 511 ∧ secp256k1ModularHalve.qubitCount = 516 := by
  have hd : (4 :: List.range' 5 255).length = (List.range' 260 256).length := by simp
  have hk : (4 :: List.range' 5 255).length = secp256k1ReductionConstantBits.length := by simp [secp256k1ReductionConstantBits]
  have hm : (4 :: List.range' 5 255).length = secp256k1ModulusBits.length := by simp [secp256k1ModulusBits]
  have hp : 2 ^ 256 - (2 ^ 32 + 977) < 2 ^ (4 :: List.range' 5 255).length := by decide
  have hodd : (2 ^ 256 - (2 ^ 32 + 977)) % 2 = 1 := by decide
  have hv : boolWordToNat secp256k1ReductionConstantBits =
      2 ^ (4 :: List.range' 5 255).length - (2 ^ 256 - (2 ^ 32 + 977)) := by
    rw [secp256k1ReductionConstant_value]; decide
  have hmod : boolWordToNat secp256k1ModulusBits = 2 ^ 256 - (2 ^ 32 + 977) := by decide
  have hl := (doubling_layout (List.range' 4 256) (List.range' 260 256) 1 2 3 0 halveProduction_layout).1
  have hw : secp256k1ModularHalve.WellFormed := modularHalve_wellFormed 4 (List.range' 5 255)
    (List.range' 260 256) _ _ 1 2 3 0 hm hd halveProduction_layout
  have ha := modularDoubleIdealState_correct 4 0 (List.range' 5 255) _ _ s hl hf hk hp hx hodd hv
  have hundo := modularHalveIdealState_after_double 4 0 (List.range' 5 255) _ _ _ s
    hl hf hk hm hp hx hodd hv hmod
  dsimp only
  refine ⟨?_,Quantum.AdaptiveCircuit.run_bornMass_eq_one _ hw _ (Quantum.normSq_ket _),hw,
    halveProduction_counts.1,halveProduction_counts.2.1,halveProduction_counts.2.2.1,
    halveProduction_counts.2.2.2,halveProduction_qubits⟩
  intro branch hb
  have h := modularHalve_branch_correct 4 (List.range' 5 255) (List.range' 260 256) _ _ 1 2 3 0 _
    hm hd halveProduction_layout ((ha.2 1 (by simp)).trans hc)
    ((ha.2 2 (by simp)).trans hr) ((ha.2 3 (by simp)).trans ht) branch hb
  have hz : secp256k1ModulusBits.all (fun k => !k) = false := by decide
  have hshort : ¬ (2 ^ 256 - (2 ^ 32 + 977) = 0 ∨
      2 ^ (4 :: List.range' 5 255).length ≤ 2 ^ 256 - (2 ^ 32 + 977)) := by decide
  simpa only [hundo,hz,Bool.false_eq_true,if_false,if_neg hshort,List.length_take,List.length_range'] using h

end ShorECDLP.Paper2607_13816
