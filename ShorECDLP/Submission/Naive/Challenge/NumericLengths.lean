import ShorECDLP.Submission.Naive.Challenge.Certificate

namespace ShorECDLP.NaiveChallenge
open Quantum Secp256k1 Challenge Arithmetic

@[simp] theorem copyReg_length_le (src dst : List Wire) : (copyReg src dst).length ≤ src.length := by
  induction src generalizing dst with
  | nil => cases dst <;> simp [copyReg]
  | cons s src ih => cases dst <;> simp [copyReg, ih]

@[simp] theorem loadConst_length_le (ws : List Wire) (c : Nat) : (loadConst ws c).length ≤ ws.length := by
  induction ws generalizing c with
  | nil => rfl
  | cons w ws ih =>
    simp only [loadConst, List.length_append, List.length_cons]
    split <;> simp only [List.length_cons, List.length_nil] <;> have := ih (c/2) <;> omega

theorem inPlaceAdd_length_le (src dst : List Wire) (carry out : Wire) :
    (inPlaceAddCarry src dst carry out).length ≤ 6*src.length+1 := by
  induction src generalizing dst carry with
  | nil => cases dst <;> simp [inPlaceAddCarry]
  | cons s src ih =>
    cases dst with
    | nil => simp [inPlaceAddCarry]
    | cons d dst =>
      have h := ih dst s
      simp only [inPlaceAddCarry, List.length_append, cuccaroMajority, cuccaroUnmajorityAdd,
        List.length_cons, List.length_nil] at h ⊢
      omega

theorem subPrepare_length (src : List Wire) (carry : Wire) :
    (subPrepare src carry).length = src.length+1 := by
  have h : (complementReg src).length = src.length := by
    induction src with
    | nil => rfl
    | cons w ws ih => simpa only [complementReg, List.length_cons] using congrArg Nat.succ ih
  simp [subPrepare, h]

theorem inPlaceSub_length_le (src dst : List Wire) (carry out : Wire) :
    (inPlaceSubCarry src dst carry out).length ≤ 8*src.length+3 := by
  have h := inPlaceAdd_length_le src dst carry out
  simp only [inPlaceSubCarry, List.length_append, List.length_reverse, subPrepare_length]
  omega

theorem lessThan_length_le (src dst : List Wire) (carry out flag : Wire) :
    (lessThanXor src dst carry out flag).length ≤ 16*src.length+8 := by
  have h := inPlaceSub_length_le src dst carry out
  simp only [lessThanXor, List.length_append, List.length_reverse, List.length_cons, List.length_nil]
  omega

theorem maskReg_length_le (control : Wire) (src dst : List Wire) :
    (ModMul.maskReg control src dst).length ≤ src.length := by
  induction src generalizing dst with
  | nil => cases dst <;> simp [ModMul.maskReg]
  | cons s src ih => cases dst <;> simp [ModMul.maskReg, ih]

theorem negativeMask_length_le (control : Wire) (src dst : List Wire) :
    (negativeMask control src dst).length ≤ src.length+2 := by
  have h := maskReg_length_le control src dst
  simp only [negativeMask, List.length_append, List.length_cons, List.length_nil]
  omega

theorem shiftLeft_length (ws : List Wire) (carry : Wire) :
    (shiftLeftCarry ws carry).length = 3*ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [shiftLeftCarry, List.length_append, swapWire, List.length_cons,
      List.length_nil, ih]; omega

theorem reduce_length_le (m dst mask : List Wire) (carry branch overflow : Wire) :
    (reduceWithFlag m dst mask carry branch overflow).length ≤ 10*m.length+6*mask.length+10 := by
  have h1 := inPlaceSub_length_le m dst carry branch
  have h2 := negativeMask_length_le branch m mask
  have h3 := inPlaceAdd_length_le mask dst carry overflow
  simp only [reduceWithFlag, List.length_append, List.length_reverse, List.length_cons, List.length_nil]
  omega

theorem double_length_le (m : List Wire) (low : Wire) (high mask : List Wire)
    (carry branch overflow : Wire) :
    (modularDouble m low high mask carry branch overflow).length ≤
      3*(high.length+1)+10*m.length+6*mask.length+11 := by
  have h := reduce_length_le m (low::high) mask carry branch overflow
  simp only [modularDouble, List.length_append, shiftLeft_length, List.length_cons, List.length_nil]
  omega

theorem controlledModAdd_length_le (control : Wire) (src m dst mask : List Wire)
    (carry branch overflow : Wire) :
    (controlledModAdd control src m dst mask carry branch overflow).length ≤
      4*src.length+10*m.length+28*mask.length+19 := by
  have h1 := maskReg_length_le control src mask
  have h2 := inPlaceAdd_length_le mask dst carry overflow
  have h3 := reduce_length_le m dst mask carry branch overflow
  have h4 := lessThan_length_le mask dst carry overflow branch
  simp only [controlledModAdd, List.length_append, List.length_reverse]
  omega

theorem horner_length_le (src m : List Wire) (low : Wire) (high mask : List Wire)
    (carry branch overflow : Wire) (controls : List Wire) :
    (LowSpaceModMul.horner src m low high mask carry branch overflow controls).length ≤
      controls.length * (3*(high.length+1)+20*m.length+34*mask.length+4*src.length+30) := by
  induction controls with
  | nil => simp [LowSpaceModMul.horner]
  | cons c cs ih =>
    have h1 := double_length_le m low high mask carry branch overflow
    have h2 := controlledModAdd_length_le c src m (low::high) mask carry branch overflow
    simp only [LowSpaceModMul.horner, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem lowSpaceProgram_length_le (modulus : Nat) (src controls m : List Wire)
    (low : Wire) (high mask : List Wire) (carry branch overflow : Wire) :
    (LowSpaceModMul.program modulus src controls m low high mask carry branch overflow).length ≤
      2*m.length + controls.length *
      (3*(high.length+1)+20*m.length+34*mask.length+4*src.length+30) := by
  have h1 := horner_length_le src m low high mask carry branch overflow controls
  have h2 := loadConst_length_le m modulus
  simp only [LowSpaceModMul.program, List.length_append, List.length_reverse]
  omega

theorem selectPoint_length_le (flag : Wire) (xs ys zs : List Wire) :
    (selectPoint flag xs ys zs).length ≤ 4*xs.length := by
  induction xs generalizing ys zs with
  | nil => cases ys <;> cases zs <;> simp [selectPoint]
  | cons x xs ih =>
    cases ys with
    | nil => simp [selectPoint]
    | cons y ys =>
      cases zs with
      | nil => simp [selectPoint]
      | cons z zs =>
        have h := ih ys zs
        simp only [selectPoint, List.length_append, selectBit, List.length_cons, List.length_nil]
        omega

theorem secpMulProgram_length_le (lhs rhs out modulus scratch : Nat) :
    (Secp256k1Instance.mulProgram lhs rhs out modulus scratch).length ≤ 4037213 := by
  have h := lowSpaceProgram_length_le p
    (Secp256k1Instance.reg lhs).wires (Secp256k1Instance.reg rhs).wires
    (Secp256k1Instance.reg modulus).wires (Secp256k1Instance.bitWire out)
    (Secp256k1Instance.regHigh out) (Secp256k1Instance.reg scratch).wires
    (Secp256k1Instance.mulCarry scratch) (Secp256k1Instance.mulBranch scratch)
    (Secp256k1Instance.mulOverflow scratch)
  simpa only [Secp256k1Instance.mulProgram, ModExp.Reg.length_eq,
    Secp256k1Instance.regHigh, List.length_range', Secp256k1Instance.fieldWidth] using h

theorem selectReg_length_le {width : Nat} (flag : Wire) (a b c : ModExp.Reg width) :
    (ModExp.selectReg flag a b c).length ≤ 4*width := by
  simpa only [ModExp.selectReg, ModExp.Reg.length_eq] using
    selectPoint_length_le flag a.wires b.wires c.wires

attribute [local irreducible] Secp256k1Instance.mulProgram ModExp.selectReg copyReg

open Secp256k1Instance in
theorem buildSchedule_length_le (bits : List Wire)
    (accId powerId historyStart duplicateId mulAccId mulStart : Nat)
    (ha : accId < historyStart) (hp : powerId < historyStart)
    (hne : accId ≠ powerId) (hb : historyStart + historyCount bits.length ≤ duplicateId)
    (hd : duplicateId < mulAccId) (hm : mulAccId < mulStart) :
    (buildSchedule bits accId powerId historyStart duplicateId mulAccId mulStart
      ha hp hne hb hd hm).schedule.forward.length ≤ bits.length * 8075968 := by
  induction bits using List.twoStepInduction generalizing accId powerId historyStart with
  | nil => simp [buildSchedule, ModExp.Schedule.forward]
  | singleton bit =>
    simp only [buildSchedule, ModExp.Schedule.forward, List.length_append, mulCall,
      List.length_cons, List.length_nil]
    have h1 := secpMulProgram_length_le powerId accId historyStart mulAccId mulStart
    have h2 := selectReg_length_le bit (reg accId) (reg historyStart) (reg (historyStart+1))
    change _ ≤ 8075968
    change _ ≤ 1028 at h2
    omega
  | cons_cons bit next bits ih0 ih =>
    have ht := ih next (historyStart+2) historyStart (historyStart+3)
      (by omega) (by omega) (by omega)
      (by simp only [List.length_cons, historyCount] at hb ⊢; omega)
    simp only [buildSchedule, ModExp.Schedule.forward, List.length_append,
      List.length_reverse, mulCall]
    have h1 := secpMulProgram_length_le powerId accId (historyStart+1) mulAccId mulStart
    have h2 := secpMulProgram_length_le powerId duplicateId historyStart mulAccId mulStart
    have h3 := selectReg_length_le bit (reg accId) (reg (historyStart+1)) (reg (historyStart+2))
    have h4 := copyReg_length_le (reg powerId).wires (reg duplicateId).wires
    change _ ≤ 1028 at h3
    simp only [ModExp.Reg.length_eq, fieldWidth] at h4
    simp only [List.length_cons] at ht ⊢
    omega

theorem plan_program_length_le {width modulus : Nat} (plan : ModExp.Plan width modulus) :
    plan.program.length ≤ 2 * plan.schedule.forward.length + 3 * width := by
  have h1 := loadConst_length_le plan.initialAcc.wires 1
  have h2 := copyReg_length_le plan.finalAcc.wires plan.out.wires
  simp only [ModExp.Reg.length_eq] at h1 h2
  simp only [ModExp.Plan.program, ModExp.Plan.compute, ModExp.initOne,
    List.length_append, List.length_reverse]
  omega

attribute [local irreducible] Secp256k1Instance.mulWork Secp256k1Instance.duplicateId Secp256k1Instance.mulAccId Secp256k1Instance.mulStartId Secp256k1Instance.historyCount Secp256k1Instance.reg Secp256k1Instance.buildSchedule Secp256k1Instance.secpSchedule Secp256k1Instance.secpPlan Secp256k1Instance.secpProgram

open Secp256k1Instance in
theorem secpSchedule_length_le : secpSchedule.schedule.forward.length ≤ 257 * 8075968 := by
  have h := buildSchedule_length_le (reg exponentId).wires initialAccId baseId
    historyStartId duplicateId mulAccId mulStartId
    (by norm_num [initialAccId, historyStartId])
    (by norm_num [baseId, historyStartId]) (by norm_num [initialAccId, baseId])
    (by simp only [ModExp.Reg.length_eq, duplicateId]; exact Nat.le_refl _) (by simp [mulAccId]) (by simp [mulStartId])
  simpa only [secpSchedule, ModExp.Reg.length_eq, fieldWidth] using h

open Secp256k1Instance in
theorem secpProgram_length_le : secpProgram.length ≤ 4151048323 := by
  have hp := @plan_program_length_le fieldWidth p secpPlan
  have h : secpPlan.schedule.forward.length ≤ 257 * 8075968 := by
    simpa only [secpPlan] using secpSchedule_length_le
  have hn : 2 * secpPlan.schedule.forward.length + 3 * fieldWidth ≤ 4151048323 := by
    simp only [fieldWidth]
    omega
  simpa only [secpProgram] using hp.trans hn

theorem ripple_length_le (a b s : List Wire) (cin : Wire) (cs : List Wire) :
    (ripple a b s cin cs).length ≤ 6*a.length := by
  induction a generalizing b s cin cs with
  | nil => cases b <;> cases s <;> cases cs <;> simp [ripple]
  | cons a as ih =>
    cases b with
    | nil => simp [ripple]
    | cons b bs =>
      cases s with
      | nil => simp [ripple]
      | cons s ss =>
        cases cs with
        | nil => simp [ripple]
        | cons c cs =>
          have h := ih bs ss c cs
          simp only [ripple, fullAdder, List.length_append, List.length_cons, List.length_nil]
          omega

theorem addConst_length_le (a c s : List Wire) (cin : Wire) (cs : List Wire) (v : Nat) :
    (addConst a c s cin cs v).length ≤ 6*a.length+2*c.length := by
  have h1 := ripple_length_le a c s cin cs
  have h2 := loadConst_length_le c v
  simp only [addConst, List.length_append]
  omega

theorem modAdd_length_le (lhs rhs out sum c candidate : List Wire)
    (ci : Wire) (cs : List Wire) (di : Wire) (ds : List Wire) (m : Nat) :
    (modAdd lhs rhs out sum c candidate ci cs di ds m).length ≤
      12*lhs.length+16*sum.length+4*c.length := by
  have h1 := ripple_length_le lhs rhs sum ci cs
  have h2 := addConst_length_le sum c candidate di ds (2^sum.length-m)
  have h3 := selectPoint_length_le (carryOut di ds) sum candidate out
  simp only [modAdd, modAddCompute, List.length_append, List.length_reverse]
  omega

theorem modSub_length_le (lhs rhs out raw c candidate : List Wire)
    (ci : Wire) (cs : List Wire) (di : Wire) (ds : List Wire) (m : Nat) :
    (modSub lhs rhs out raw c candidate ci cs di ds m).length ≤
      12*lhs.length+4*rhs.length+12*raw.length+4*c.length+4*candidate.length+4 := by
  have h1 := ripple_length_le lhs rhs raw ci cs
  have h2 := addConst_length_le raw c candidate di ds m
  have h3 := selectPoint_length_le (carryOut ci cs) candidate raw out
  simp only [modSub, modSubCompute, subRaw, List.length_append, List.length_reverse,
    subPrepare_length]
  omega

theorem copyReg_length_le_right (src dst : List Wire) :
    (copyReg src dst).length ≤ dst.length := by
  induction src generalizing dst with
  | nil => cases dst <;> simp [copyReg]
  | cons s src ih => cases dst <;> simp [copyReg, ih]

theorem binaryWrapper_length_le (a b r lhs rhs out : List Wire) (core : Circuit) :
    (copyReg lhs a ++ copyReg rhs b ++ core ++ copyReg r out ++ core.reverse ++
      copyReg rhs b ++ copyReg lhs a).length ≤
        2*lhs.length+2*rhs.length+out.length+2*core.length := by
  have h1 := copyReg_length_le lhs a
  have h2 := copyReg_length_le rhs b
  have h3 := copyReg_length_le_right r out
  simp only [List.length_append, List.length_reverse]
  omega

theorem constantWrapper_length_le (a b r lhs out : List Wire) (core : Circuit) (c : Nat) :
    (copyReg lhs a ++ loadConst b c ++ core ++ copyReg r out ++ core.reverse ++
      loadConst b c ++ copyReg lhs a).length ≤
        2*lhs.length+2*b.length+out.length+2*core.length := by
  have h1 := copyReg_length_le lhs a
  have h2 := loadConst_length_le b c
  have h3 := copyReg_length_le_right r out
  simp only [List.length_append, List.length_reverse]
  omega

theorem fieldMul_length_le (offset : Wire) (lhs rhs out : List Wire) :
    (fieldMul offset lhs rhs out).length ≤ 2*lhs.length+2*rhs.length+out.length+8074426 := by
  have h := binaryWrapper_length_le
    (shiftWires offset Secp256k1Instance.secpMulLayout.lhs)
    (shiftWires offset Secp256k1Instance.secpMulLayout.rhs)
    (shiftWires offset Secp256k1Instance.secpMulLayout.out) lhs rhs out
    (shiftCircuit offset Secp256k1Instance.secpMulProgram)
  have hc := secpMulProgram_length_le Secp256k1Instance.baseId Secp256k1Instance.exponentId
    Secp256k1Instance.outId Secp256k1Instance.initialAccId Secp256k1Instance.historyStartId
  change (fieldMul offset lhs rhs out).length ≤ _ at h
  simp only [shiftCircuit, List.length_map, Secp256k1Instance.secpMulProgram] at h
  omega

theorem fieldInv_length_le (offset : Wire) (input out : List Wire) :
    (fieldInv offset input out).length ≤ 2*input.length+out.length+8302097160 := by
  have h := constantWrapper_length_le
    (shiftWires offset Secp256k1Instance.secpLayout.lhs)
    (shiftWires offset Secp256k1Instance.secpLayout.rhs)
    (shiftWires offset Secp256k1Instance.secpLayout.out) input out
    (shiftCircuit offset Secp256k1Instance.secpProgram) (p-2)
  change (fieldInv offset input out).length ≤ _ at h
  simp only [shiftCircuit, List.length_map, shiftWires,
    Secp256k1Instance.secpLayout, ModExp.Plan.layout, Secp256k1Instance.secpPlan,
    ModExp.Reg.length_eq, Secp256k1Instance.fieldWidth] at h
  have hc := secpProgram_length_le
  omega

open Secp256k1Instance in
theorem addProgram_length_le (a b c start : Nat) : (addProgram a b c start).length ≤ 8224 := by
  simpa only [addProgram, ModExp.Reg.length_eq, fieldWidth] using
    modAdd_length_le (reg a).wires (reg b).wires (reg c).wires
      (reg start).wires (reg (start+1)).wires (reg (start+2)).wires
      (bitWire (start+3)) (reg (start+4)).wires
      (bitWire (start+5)) (reg (start+6)).wires p

theorem fieldAdd_length_le (offset : Wire) (lhs rhs out : List Wire) :
    (fieldAdd offset lhs rhs out).length ≤ 2*lhs.length+2*rhs.length+out.length+16448 := by
  have h := binaryWrapper_length_le
    (shiftWires offset Secp256k1Instance.secpAddLayout.lhs)
    (shiftWires offset Secp256k1Instance.secpAddLayout.rhs)
    (shiftWires offset Secp256k1Instance.secpAddLayout.out) lhs rhs out
    (shiftCircuit offset Secp256k1Instance.secpAddProgram)
  have hc := addProgram_length_le Secp256k1Instance.baseId Secp256k1Instance.exponentId
    Secp256k1Instance.outId Secp256k1Instance.initialAccId
  change (fieldAdd offset lhs rhs out).length ≤ _ at h
  simp only [shiftCircuit, List.length_map, Secp256k1Instance.secpAddProgram] at h
  omega

open Secp256k1Instance in
theorem fieldSub_length_le (offset : Wire) (lhs rhs out : List Wire) :
    (fieldSub offset lhs rhs out).length ≤ 2*lhs.length+2*rhs.length+out.length+18512 := by
  let core := modSub (reg 0).wires (reg 1).wires (reg 2).wires (reg 3).wires
    (reg 4).wires (reg 5).wires (bitWire 6) (reg 7).wires (bitWire 8) (reg 9).wires p
  have hc : core.length ≤ 9256 := by
    simpa only [core, ModExp.Reg.length_eq, fieldWidth] using
      modSub_length_le (reg 0).wires (reg 1).wires (reg 2).wires (reg 3).wires
        (reg 4).wires (reg 5).wires (bitWire 6) (reg 7).wires (bitWire 8) (reg 9).wires p
  have h := binaryWrapper_length_le (shiftWires offset (reg 0).wires)
    (shiftWires offset (reg 1).wires) (shiftWires offset (reg 2).wires)
    lhs rhs out (shiftCircuit offset core)
  change (fieldSub offset lhs rhs out).length ≤ _ at h
  simp only [shiftCircuit, List.length_map] at h
  omega

theorem fieldLoadGates_length_le {n : Nat} (row : Fin n) (field : PointField)
    (ws : List Wire) (i : Nat) : (fieldLoadGates row field ws i).length ≤ ws.length := by
  induction ws generalizing i with
  | nil => rfl
  | cons w ws ih =>
    simp only [fieldLoadGates, List.length_append, List.length_cons]
    split <;> simp only [List.length_cons, List.length_nil] <;> have := ih (i+1) <;> omega

open Secp256k1Instance in
theorem fieldSubConstGates_length_le {n : Nat} (row : Fin n) (field : PointField)
    (offset : Wire) (lhs out : List Wire) :
    (fieldSubConstGates row field offset lhs out).length ≤ 2*lhs.length+out.length+19026 := by
  have hc := modSub_length_le (reg 0).wires (reg 1).wires (reg 2).wires (reg 3).wires
    (reg 4).wires (reg 5).wires (bitWire 6) (reg 7).wires (bitWire 8) (reg 9).wires p
  have h1 := copyReg_length_le lhs (shiftWires offset (reg 0).wires)
  have h2 := copyReg_length_le_right (shiftWires offset (reg 2).wires) out
  have h3 := fieldLoadGates_length_le row field (shiftWires offset (reg 1).wires) 0
  simp only [shiftWires, List.length_map, ModExp.Reg.length_eq, fieldWidth] at hc h3
  simp only [shiftWires] at h1 h2
  simp only [fieldSubConstGates, shiftCircuit, shiftWires, List.length_map, List.length_append,
    List.length_reverse]
  omega


@[simp] theorem pointAddX_length (w : Wire) : (pointAddX w).length = 257 := by
  simp only [pointAddX, List.length_range']; rfl

@[simp] theorem pointAddY_length (w : Wire) : (pointAddY w).length = 257 := by
  simp only [pointAddY, List.length_range']; rfl

@[simp] theorem pointAddT0_length (w : Wire) : (pointAddT0 w).length = 257 := by
  simp only [pointAddT0, List.length_range']; rfl

@[simp] theorem pointAddT1_length (w : Wire) : (pointAddT1 w).length = 257 := by
  simp only [pointAddT1, List.length_range']; rfl

@[simp] theorem pointAddT2_length (w : Wire) : (pointAddT2 w).length = 257 := by
  simp only [pointAddT2, List.length_range']; rfl

@[simp] theorem pointAddT3_length (w : Wire) : (pointAddT3 w).length = 257 := by
  simp only [pointAddT3, List.length_range']; rfl

@[simp] theorem pointAddT4_length (w : Wire) : (pointAddT4 w).length = 257 := by
  simp only [pointAddT4, List.length_range']; rfl

@[simp] theorem pointAddConst_length (w : Wire) : (pointAddConst w).length = 256 := by
  simp only [pointAddConst, List.length_range']

@[simp] theorem pointAddXDifference_length (w : Wire) : (pointAddXDifference w).length = 256 := by
  simp only [pointAddXDifference, List.length_range']

@[simp] theorem pointAddYDifference_length (w : Wire) : (pointAddYDifference w).length = 256 := by
  simp only [pointAddYDifference, List.length_range']

@[simp] theorem pointAddCandidate_length (w : Wire) : (pointAddCandidate w).length = 513 := by
  simp only [pointAddCandidate, List.length_range']; rfl

@[simp] theorem pointAddSelected_length (w : Wire) : (pointAddSelected w).length = 513 := by
  simp only [pointAddSelected, List.length_range']; rfl

theorem threeXSquared_length_le (offset : Wire) (x a b out : List Wire)
    (hx : x.length = 257) (ha : a.length = 257) (hb : b.length = 257)
    (ho : out.length = 257) : (threeXSquared offset x a b out).length ≤ 16300000 := by
  have h1 := fieldMul_length_le offset x x a
  have h2 := fieldAdd_length_le offset a a b
  have h3 := fieldAdd_length_le offset b a out
  simp only [threeXSquared, List.length_append, List.length_reverse]
  omega

theorem genericPointGates_length_le {n : Nat} (row : Fin n) (w : Wire) :
    (genericPointGates row w).length ≤ 17000000000 := by
  simp only [genericPointGates, List.length_append, List.length_reverse, List.length_map]
  grind only [fieldSubConstGates_length_le, fieldInv_length_le, fieldMul_length_le,
    fieldSub_length_le, pointAddX_length, pointAddY_length, pointAddT0_length,
    pointAddT1_length, pointAddT2_length, pointAddT3_length, pointAddT4_length]

theorem doublePointCompute_length_le (w : Wire) :
    (doublePointCompute w).length ≤ 17000000000 := by
  have hn := threeXSquared_length_le (pointAddArithmeticOffset w) (pointAddX w)
    (pointAddT0 w) (pointAddT1 w) (pointAddT2 w) (by simp) (by simp) (by simp) (by simp)
  simp only [doublePointCompute, List.length_append, List.length_reverse]
  grind only [fieldInv_length_le, fieldMul_length_le, fieldAdd_length_le,
    fieldSub_length_le, pointAddX_length, pointAddY_length, pointAddT0_length,
    pointAddT1_length, pointAddT2_length, pointAddT3_length, pointAddT4_length]

theorem zeroCompute_length_le (ws hs : List Wire) : (zeroCompute ws hs).length ≤ 3*ws.length := by
  induction ws using List.twoStepInduction generalizing hs with
  | nil => cases hs <;> simp [zeroCompute]
  | singleton w => cases hs <;> simp [zeroCompute]
  | cons_cons w v ws ih0 ih =>
    cases hs with
    | nil => simp [zeroCompute]
    | cons h hs =>
      cases hs with
      | nil => simp [zeroCompute]
      | cons k hs =>
        have ht := ih v (k::hs)
        simp only [zeroCompute, List.length_append, List.length_cons, List.length_nil]
        simp only [List.length_cons] at ht
        omega

theorem zeroFlag_length_le (ws : List Wire) (flag : Wire) (hs : List Wire) :
    (zeroFlag ws flag hs).length ≤ 6*ws.length+1 := by
  cases ws with
  | nil => simp [zeroFlag]
  | cons w ws =>
    cases hs with
    | nil => simp [zeroFlag]
    | cons h hs =>
      have hc := zeroCompute_length_le (w::ws) (h::hs)
      simp only [zeroFlag, List.length_append, List.length_reverse, List.length_cons, List.length_nil]
      simp only [List.length_cons] at hc
      omega

theorem equalFlag_length_le (lhs rhs : List Wire) (f : Wire) (ds hs : List Wire) :
    (equalFlag lhs rhs f ds hs).length ≤ 2*lhs.length+2*rhs.length+6*ds.length+1 := by
  cases ds with
  | nil => simp [equalFlag]
  | cons d ds =>
    cases hs with
    | nil => simp [equalFlag]
    | cons h hs =>
      have h1 := copyReg_length_le lhs (d::ds)
      have h2 := copyReg_length_le rhs (d::ds)
      have h3 := zeroCompute_length_le (d::ds) (h::hs)
      simp only [equalFlag, equalCompute, List.length_append, List.length_reverse,
        List.length_cons, List.length_nil]
      simp only [List.length_cons] at h3
      omega

theorem controlledCopyReg_length_le (c : Wire) (src dst : List Wire) :
    (controlledCopyReg c src dst).length ≤ src.length := by
  induction src generalizing dst with
  | nil => simp [controlledCopyReg]
  | cons s src ih => cases dst <;> simp [controlledCopyReg, ih]

theorem pointSwapReg_length_le (src dst : List Wire) :
    (pointSwapReg src dst).length ≤ 3*src.length := by
  induction src generalizing dst with
  | nil => simp [pointSwapReg]
  | cons s src ih =>
    cases dst with
    | nil => simp [pointSwapReg]
    | cons d dst =>
      have h := ih dst
      simp only [pointSwapReg, List.length_cons]
      omega

theorem point_tag_length_le (ws : List Wire) : (PointRegister.tag ws).length ≤ 1 := by
  simp [PointRegister.tag]
theorem point_x_length_le (ws : List Wire) : (PointRegister.x ws).length ≤ 256 := by
  simp [PointRegister.x]
theorem point_y_length_le (ws : List Wire) : (PointRegister.y ws).length ≤ 256 := by
  simp [PointRegister.y]

theorem packFinitePoint_length_le (x y point : List Wire) :
    (packFinitePoint x y point).length ≤ 513 := by
  have h1 := loadConst_length_le (PointRegister.tag point) 1
  have h2 := copyReg_length_le_right (x.take 256) (PointRegister.x point)
  have h3 := copyReg_length_le_right (y.take 256) (PointRegister.y point)
  have h4 := point_tag_length_le point
  have h5 := point_x_length_le point
  have h6 := point_y_length_le point
  simp only [packFinitePoint, List.length_append]
  omega

theorem packedGate_length_le {n : Nat} (row : Fin n) (w : Wire) (i : Nat) :
    (packedGate row w i).length ≤ 1 := by
  unfold packedGate
  split <;> (try split) <;> (try split) <;> simp

theorem packedLoadGates_length_le {n : Nat} (row : Fin n) (ws : List Wire) (i : Nat) :
    (packedLoadGates row ws i).length ≤ ws.length := by
  induction ws generalizing i with
  | nil => rfl
  | cons w ws ih =>
    have h1 := packedGate_length_le row w i
    have h2 := ih (i+1)
    simp only [packedLoadGates, List.length_append, List.length_cons]
    omega

theorem pointFlagGates_length_le {n : Nat} (row : Fin n) (ps : List Wire) (w : Wire) :
    (pointFlagGates row ps w).length ≤ 6164 := by
  simp only [pointFlagGates, List.length_append, List.length_map, List.length_cons, List.length_nil]
  grind only [zeroFlag_length_le, equalFlag_length_le, fieldLoadGates_length_le,
    point_tag_length_le, point_x_length_le, point_y_length_le, pointAddConst_length,
    pointAddXDifference_length, pointAddYDifference_length]

theorem genericBranchGates_length_le {n : Nat} (row : Fin n) (w : Wire) :
    (genericBranchGates row w).length ≤ 34000001539 := by
  simp only [genericBranchGates, List.length_append, List.length_map, List.length_reverse]
  grind only [genericPointGates_length_le, packFinitePoint_length_le,
    controlledCopyReg_length_le, pointAddCandidate_length]

theorem doublePointBranch_length_le (w : Wire) :
    (doublePointBranch w).length ≤ 34000001539 := by
  simp only [doublePointBranch, List.length_append, List.length_reverse]
  grind only [doublePointCompute_length_le, packFinitePoint_length_le,
    controlledCopyReg_length_le, pointAddCandidate_length]

theorem infinityBranchGates_length_le {n : Nat} (row : Fin n) (w : Wire) :
    (infinityBranchGates row w).length ≤ 1539 := by
  simp only [infinityBranchGates, List.length_append, List.length_map]
  grind only [packedLoadGates_length_le, controlledCopyReg_length_le, pointAddCandidate_length]

theorem pointAddCoordinateCopies_length_le (ps : List Wire) (w : Wire) :
    (pointAddCoordinateCopies ps w).length ≤ 512 := by
  simp only [pointAddCoordinateCopies, pointAddCopyX, pointAddCopyY, List.length_append]
  grind only [copyReg_length_le, point_x_length_le, point_y_length_le]

theorem finiteComputeGates_length_le {n : Nat} (row : Fin n) (ps : List Wire) (w : Wire) :
    (finiteComputeGates row ps w).length ≤ 68000012000 := by
  simp only [finiteComputeGates, List.length_append, List.length_map]
  grind only [pointAddCoordinateCopies_length_le, pointFlagGates_length_le,
    genericBranchGates_length_le, doublePointBranch_length_le, infinityBranchGates_length_le]

theorem controlledOutGates_length_le {n : Nat} (row : Fin n) (c : Wire)
    (ps out : List Wire) (w : Wire) (hp : ps.length = 513) (ho : out.length = 513) :
    (controlledOutGates row c ps out w).length ≤ 136000030000 := by
  have hc := finiteComputeGates_length_le row ps (controlledPointAddPointWorkStart w)
  have hs := selectPoint_length_le c ps (pointAddSelected (controlledPointAddPointWorkStart w))
    (controlledPointAddChoice w)
  have h1 := copyReg_length_le_right (controlledPointAddChoice w) out
  have h2 := copyReg_length_le ps out
  simp only [controlledOutGates, finiteControlledOutGates, List.length_append,
    List.length_reverse, List.length_map]
  omega

theorem controlledPointGates_length_le {n : Nat} (row : Fin n) (c : Wire)
    (ps : List Wire) (w : Wire) (hp : ps.length = 513) :
    (controlledPointGates row c ps w).length ≤ 300000000000 := by
  have ht : (controlledPointAddTemp w).length = 513 := by
    simp only [controlledPointAddTemp, List.length_range']; rfl
  have h1 := controlledOutGates_length_le row c ps (controlledPointAddTemp w)
    (controlledPointAddAuxStart w) hp ht
  have h2 := controlledOutGates_length_le (0 : Fin 1) c ps (controlledPointAddTemp w)
    (controlledPointAddAuxStart w) hp ht
  have h3 := pointSwapReg_length_le ps (controlledPointAddTemp w)
  simp only [controlledPointGates, negControlledOutGates, List.length_append,
    List.length_reverse, List.length_map]
  omega

theorem scalarGates_length_le {n : Nat} (ps : List Wire) (w : Wire)
    (cs : List Wire) (rs : List (Fin n)) (hp : ps.length = 513) :
    (scalarGates ps w cs rs).length ≤ cs.length * 300000000000 := by
  induction cs generalizing rs with
  | nil => cases rs <;> simp [scalarGates]
  | cons c cs ih =>
    cases rs with
    | nil => simp [scalarGates]
    | cons r rs =>
      have h1 := controlledPointGates_length_le r c ps w hp
      have h2 := ih rs
      simp only [scalarGates, List.length_append, List.length_cons]
      omega

theorem qftPhaseLayer_length (t a : Wire) (ws : List Wire) (k : Nat) :
    (qftPhaseLayer t a ws k).length = 3*ws.length := by
  induction ws generalizing k with
  | nil => rfl
  | cons w ws ih => simp [qftPhaseLayer, cPhase, ih]; omega

theorem qftCoreMSB_length_le (a : Wire) (ws : List Wire) :
    (qftCoreMSB a ws).length ≤ 3*ws.length^2+ws.length := by
  induction ws with
  | nil => simp [qftCoreMSB]
  | cons w ws ih =>
    simp only [qftCoreMSB, List.length_append, List.length_cons, List.length_nil, qftPhaseLayer_length]
    nlinarith

theorem bitReverse_length_le (ws : List Wire) : (bitReverse ws).length ≤ 3*ws.length := by
  have he : ∀ ps : List (Wire × Wire), (ps.flatMap (fun p => swap p.1 p.2)).length = 3*ps.length := by
    intro ps
    induction ps with
    | nil => rfl
    | cons p ps ih => simp [List.flatMap_cons, swap]; omega
  simp only [bitReverse, he, List.length_take, List.length_zip, List.length_reverse, min_self]
  omega

theorem iqft_length_le (ws : List Wire) (a : Wire) :
    (iqft ws a).length ≤ 3*ws.length^2+4*ws.length := by
  have h1 := qftCoreMSB_length_le a ws.reverse
  have h2 := bitReverse_length_le ws
  simp only [List.length_reverse] at h1
  simp only [iqft, Circuit.adjoint, qft, qftCore, List.length_map,
    List.length_reverse, List.length_append]
  omega

theorem trialGates_length_le : trialGates.length ≤ 153600000400000 := by
  have hp : bitcoinPointReg.length = 513 := by
    simp only [bitcoinPointReg, List.length_range']; rfl
  have h1 := scalarGates_length_le bitcoinPointReg bitcoinWorkStart bitcoinAReg gPowerRows hp
  have h2 := scalarGates_length_le bitcoinPointReg bitcoinWorkStart bitcoinBReg qPowerRows hp
  have h3 := iqft_length_le bitcoinAReg bitcoinQFTAncilla
  have h4 := iqft_length_le bitcoinBReg bitcoinQFTAncilla
  simp only [bitcoinAReg, bitcoinBReg, List.length_range'] at h1 h2 h3 h4
  simp only [trialGates, List.length_append, List.length_map, PhaseEstimation.hadamards]
  simp only [bitcoinAReg, bitcoinBReg, List.length_range']
  omega

theorem gateSlots_castTable {n m s e : Nat} (h : n = m) (p : Straight n s e) :
    (castTable h p).gateSlots = p.gateSlots := by cases h; rfl

attribute [local irreducible] trialGates fixedResetWires repeatedProgram naivePowerTable

theorem append_reset_gateSlots {n s e : Nat} (p : Straight n s e) (ws : List Wire) :
    (p.append (resetWireProgram ws e)).gateSlots = p.gateSlots := by
  rw [Straight.gateSlots_append, resetWireProgram_gateSlots, Nat.add_zero]

theorem roundProgram_gateSlots_eq (cursor : Nat) :
    (roundProgram cursor).gateSlots = trialGates.length+1024 := by
  unfold roundProgram
  rw [gateSlots_castFinish]
  unfold roundProgramRaw
  rw [append_reset_gateSlots]
  exact observedTrialProgram_slots cursor

theorem roundProgram_gateSlots_le (cursor : Nat) :
    (roundProgram cursor).gateSlots ≤ 153600000401024 := by
  rw [roundProgram_gateSlots_eq]
  exact Nat.add_le_add_right trialGates_length_le 1024

theorem repeatedProgram_gateSlots_le (count cursor : Nat) :
    (repeatedProgram count cursor).gateSlots ≤ count*153600000401024 := by
  induction count generalizing cursor with
  | zero => simp only [repeatedProgram, gateSlots_castFinish, Straight.gateSlots, Nat.zero_mul, le_refl]
  | succ count ih =>
    have h1 := roundProgram_gateSlots_le cursor
    have h2 := ih (cursor+207136)
    simp only [repeatedProgram, gateSlots_castFinish, Straight.gateSlots_append]
    omega

theorem naiveRepeatedEntry_gateSlots_le :
    naiveRepeatedEntry.program.gateSlots ≤ 4000000000000000 := by
  simp only [naiveRepeatedEntry, gateSlots_castTable]
  exact (repeatedProgram_gateSlots_le 26 0).trans (by decide)

end ShorECDLP.NaiveChallenge
