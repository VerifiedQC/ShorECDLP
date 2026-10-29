import ShorECDLP.Submission.«2607_13816».Challenge.LookupSlots
import ShorECDLP.Submission.«2607_13816».Arithmetic.UnitaryPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.EndpointPrimitiveCounts
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

def nonCarryCost : Gate → Nat
  | .CX _ _ | .CCX _ _ _ => 0
  | _ => 1

theorem circuit_length_carry (gs : Circuit) :
    gs.length = eeaCnotCount gs + eeaToffoliCount gs + (gs.map nonCarryCost).sum := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases g <;> simp_all [eeaCnotCount,eeaToffoliCount,nonCarryCost] <;> omega

theorem carryXor_length_le (input dirty : List Wire) (constant : List Bool) (q c : Wire)
    (hd : input.length = dirty.length) (hk : constant.length = input.length) :
    (controlledConstCarryXor input dirty constant q c).length ≤ 9*input.length := by
  have hw (bs : List Bool) : constantBitWeight bs ≤ bs.length := by
    induction bs with
    | nil => rfl
    | cons b bs ih =>
      cases b <;> simp only [constantBitWeight,List.map_cons,List.sum_cons,List.length_cons,
        Bool.toNat_false,Bool.toNat_true] at ih ⊢ <;> omega
  cases input with
  | nil => simp [controlledConstCarryXor]
  | cons a input =>
    cases constant with
    | nil => simp at hk
    | cons k constant =>
      have h := controlledConstCarryXor_counts a input dirty k constant q c (by simpa using hk.symm) hd
      have hz := controlledConstCarryXor_cost_zero nonCarryCost (by intros; rfl) (by intros; rfl)
        (a::input) dirty (k::constant) q c
      have hwc := hw constant
      rw [circuit_length_carry,h.2.1,h.2.2.1,hz]
      have hb : k.toNat ≤ 1 := by cases k <;> decide
      simp only [List.length_cons] at hk ⊢
      omega

theorem gidneyAddCleanup_length_le (input dirty : List Wire) (constant : List Bool) (q c : Wire)
    (hd : input.length = dirty.length+1) (hk : constant.length=input.length) :
    (gidneyAddCleanup input dirty constant q c).length ≤ 11*input.length := by
  have h := carryXor_length_le (input.take dirty.length) dirty (constant.take dirty.length) q c
    (by simp only [List.length_take]; omega) (by simp only [List.length_take]; omega)
  simp only [gidneyAddCleanup,gidneyFlipWord,List.length_append,List.length_map]
  simp only [List.length_take] at h
  omega

theorem deferredCorrectionSlots_le (targets cleanup prior : Nat) (cells : List (Circuit × Wire)) :
    deferredCorrectionSlots targets cleanup prior cells ≤
      (cells.map (fun c => c.1.length)).sum + 6*targets + cleanup := by
  induction cells generalizing prior with
  | nil => simp only [deferredCorrectionSlots,List.map_nil,List.sum_nil]; omega
  | cons c cells ih =>
    rcases c with ⟨gs,w⟩
    simp only [deferredCorrectionSlots,List.map_cons,List.sum_cons]
    have h := ih (prior+1)
    omega

theorem gidneyCarryCells_slots_le (q current spare ancilla : Wire)
    (input dirty : List Wire) (constant : List Bool)
    (hd : input.length=dirty.length+1) (hk : constant.length=input.length) :
    ((gidneyCarryCells q current spare ancilla input dirty constant).map (fun c => c.1.length)).sum ≤
      9*input.length := by
  induction input generalizing current spare dirty constant with
  | nil => simp at hd
  | cons a input ih =>
    cases constant with
    | nil => simp at hk
    | cons k ks =>
      cases input with
      | nil =>
        have hd' : dirty=[] := List.eq_nil_of_length_eq_zero (by simp_all)
        have hk' : ks=[] := List.eq_nil_of_length_eq_zero (by simp_all)
        subst dirty; subst ks
        cases k <;> simp [gidneyCarryCells]
      | cons b bs =>
        cases dirty with
        | nil => simp at hd
        | cons d ds =>
          have h := ih spare current ds ks (by simpa using hd) (by simpa using hk)
          simp only [gidneyCarryCells,List.map_cons,List.sum_cons,List.length_cons]
          have hc : (gidneyAddCarryCell q current spare ancilla a d k).length ≤ 9 := by
            cases k <;> simp [gidneyAddCarryCell]
          simp only [List.length_cons] at h
          omega
theorem gidneyNontrivialProgram_slots_le (n start : Nat) (a d q carry spare ancilla : Wire)
    (as ds : List Wire) (k : Bool) (ks : List Bool)
    (hd : as.length=ds.length+1) (hk : ks.length=as.length) :
    (gidneyNontrivialProgram n start a d q carry spare ancilla as ds k ks).gateSlots ≤
      26*(as.length+1) := by
  have ht := gidneyCarryCells_slots_le q spare carry ancilla as ds ks hd hk
  have hc := gidneyAddCleanup_length_le (a::as) (d::ds) (k::ks) q carry
    (by simp only [List.length_cons]; omega) (by simp only [List.length_cons]; omega)
  have hf : (gidneyAddCarryCell q carry spare ancilla a d k).length ≤ 9 := by
    cases k <;> simp [gidneyAddCarryCell]
  have hb := deferredCorrectionSlots_le (d::ds).length
    (gidneyAddCleanup (a::as) (d::ds) (k::ks) q carry).length 0
    (gidneyCarryCells q spare carry ancilla as ds ks)
  simp only [gidneyNontrivialProgram,Straight.gateSlots_append,literalProgram_slots,
    deferredCorrectionProgram_slots,List.length_nil,List.length_cons]
  simp only [List.length_cons] at hc hb
  omega

theorem gidneyProgram_slots_le (n start : Nat) (input dirty : List Wire) (constant : List Bool)
    (q carry spare ancilla : Wire) (hd : input.length=dirty.length+1)
    (hk : constant.length=input.length) :
    (gidneyProgram n start input dirty constant q carry spare ancilla).2.gateSlots ≤ 26*input.length := by
  by_cases hz : constant.all (fun k => !k) = true
  · rw [show gidneyProgram n start input dirty constant q carry spare ancilla = ⟨0,.done⟩ by simp only [gidneyProgram,hz,ite_true]]; exact Nat.zero_le _
  · rw [show gidneyProgram n start input dirty constant q carry spare ancilla = _ by exact if_neg hz]
    cases input with
    | nil => simp at hd
    | cons a as =>
      cases constant with
      | nil => simp at hk
      | cons k ks =>
        cases dirty with
        | nil =>
          have ha : as=[] := List.eq_nil_of_length_eq_zero (by simp_all)
          have hks : ks=[] := List.eq_nil_of_length_eq_zero (by simp_all)
          subst as; subst ks
          cases k <;> simp [literalProgram_slots]
        | cons d ds =>
          have h := gidneyNontrivialProgram_slots_le n start a d q carry spare ancilla as ds k ks
            (by simpa using hd) (by simpa using hk)
          cases as with
          | nil => simp at hd
          | cons b bs => exact h

theorem compareCarryCell_length_le (q c r t a d f : Wire) (k last : Bool) :
    (gidneyCompareCarryCell q c r t a d f k last).length ≤ 10 := by
  cases k <;> cases last <;> simp [gidneyCompareCarryCell]

theorem compareCarryCells_slots_le (q current spare ancilla flag : Wire)
    (input dirty : List Wire) (constant : List Bool)
    (hd : input.length=dirty.length) (hk : constant.length=input.length) :
    ((compareCarryCells q current spare ancilla flag input dirty constant).map (fun c => c.1.length)).sum ≤
      10*input.length := by
  induction input generalizing current spare dirty constant with
  | nil =>
    have hd' : dirty=[] := List.eq_nil_of_length_eq_zero hd.symm
    have hk' : constant=[] := List.eq_nil_of_length_eq_zero hk
    subst dirty; subst constant
    rfl
  | cons a input ih =>
    cases constant with
    | nil => simp at hk
    | cons k ks =>
      cases dirty with
      | nil => simp at hd
      | cons d ds =>
        have h := ih spare current ds ks (by simpa using hd) (by simpa using hk)
        have hc := compareCarryCell_length_le q current spare ancilla a d flag k input.isEmpty
        simp only [compareCarryCells,List.map_cons,List.sum_cons,List.length_cons]
        omega

theorem compareCarryProgram_slots_le (n start : Nat) (a d q carry spare ancilla flag : Wire)
    (input dirty : List Wire) (k : Bool) (constant : List Bool)
    (hd : input.length=dirty.length) (hk : constant.length=input.length) :
    (compareCarryProgram n start a d q carry spare ancilla flag input dirty k constant).gateSlots ≤
      25*(input.length+1) := by
  have ht := compareCarryCells_slots_le q spare carry ancilla flag input dirty constant hd hk
  have hc := carryXor_length_le (a::input) (d::dirty) (k::constant) q carry
    (by simp only [List.length_cons]; omega) (by simp only [List.length_cons]; omega)
  have hf := compareCarryCell_length_le q carry spare ancilla a d flag k input.isEmpty
  have hb := deferredCorrectionSlots_le (d::dirty).length
    (controlledConstCarryXor (a::input) (d::dirty) (k::constant) q carry).length 0
    (compareCarryCells q spare carry ancilla flag input dirty constant)
  simp only [compareCarryProgram,Straight.gateSlots_append,literalProgram_slots,
    deferredCorrectionProgram_slots,List.length_nil,List.length_cons]
  simp only [List.length_cons] at hc hb
  omega

theorem compareCoreProgram_slots_le (n start : Nat) (input dirty : List Wire) (constant : List Bool)
    (q carry spare ancilla flag : Wire) (hd : input.length=dirty.length)
    (hk : constant.length=input.length) :
    (compareCoreProgram n start input dirty constant q carry spare ancilla flag).2.gateSlots ≤ 25*input.length := by
  cases input with
  | nil => simp [compareCoreProgram,Straight.gateSlots]
  | cons a input =>
    cases dirty with
    | nil => simp at hd
    | cons d dirty =>
      cases constant with
      | nil => simp at hk
      | cons k constant =>
        exact compareCarryProgram_slots_le n start a d q carry spare ancilla flag input dirty k constant
          (by simpa using hd) (by simpa using hk)

theorem compareGEProgram_slots_le (n start : Nat) (input dirty : List Wire) (threshold : Nat)
    (q carry spare ancilla flag : Wire) (hd : input.length=dirty.length) :
    (compareGEProgram n start input dirty threshold q carry spare ancilla flag).2.gateSlots ≤ 25*input.length+1 := by
  by_cases hz : threshold=0
  · rw [show compareGEProgram n start input dirty threshold q carry spare ancilla flag = ⟨0,literalProgram [.CX q flag]⟩ by exact if_pos hz]
    simp only [literalProgram_slots,List.length_cons,List.length_nil]; omega
  · by_cases hh : 2^input.length ≤ threshold
    · rw [show compareGEProgram n start input dirty threshold q carry spare ancilla flag = ⟨0,.done⟩ by simp only [compareGEProgram, hz,ite_false,hh,ite_true]]
      exact Nat.zero_le _
    · rw [show compareGEProgram n start input dirty threshold q carry spare ancilla flag = _ by exact if_neg hz]
      rw [if_neg hh]
      have h := compareCoreProgram_slots_le n start input dirty
        ((List.range input.length).map (Nat.testBit (2^input.length-threshold))) q carry spare ancilla flag hd
        (by simp only [List.length_map,List.length_range])
      omega

theorem appendCompiled_slots {n start : Nat} (p : (count : Nat) × Straight n start (start+count))
    (q : (count : Nat) × Straight n (start+p.1) (start+p.1+count)) :
    (appendCompiled p q).2.gateSlots = p.2.gateSlots+q.2.gateSlots := by
  simp only [appendCompiled,castFinish_gateSlots,Straight.gateSlots_append]

theorem prependCompiled_slots {n start : Nat} (gs : Circuit)
    (p : (count : Nat) × Straight n start (start+count)) :
    (prependCompiled gs p).2.gateSlots = gs.length+p.2.gateSlots := by
  simp only [prependCompiled,Straight.gateSlots_append,literalProgram_slots]

attribute [local irreducible] compareGEProgram gidneyProgram

theorem modularNegateProgram_slots_le (n start : Nat) (target dirty : List Wire) (modulus : List Bool)
    (q c r t f : Wire) (hd : target.length=dirty.length) (hk : modulus.length=target.length)
    (hpos : 0<target.length) :
    (modularNegateProgram n start target dirty modulus q c r t f).2.gateSlots ≤ 103*target.length+2 := by
  have htake : target.length=(dirty.take (target.length-1)).length+1 := by
    simp only [List.length_take]; omega
  have ht (s : Nat) := compareGEProgram_slots_le n s target dirty 1 q c r t f hd
  have hi (s : Nat) := gidneyProgram_slots_le n s target (dirty.take (target.length-1))
    ((List.range target.length).map (Nat.testBit 1)) q c r t htake
    (by simp only [List.length_map,List.length_range])
  have ha (s : Nat) := gidneyProgram_slots_le n s target (dirty.take (target.length-1)) modulus f c r t htake hk
  simp only [modularNegateProgram,appendCompiled_slots,prependCompiled_slots]
  have hc : (controlledComplement target q).length=target.length := by
    simp only [controlledComplement,List.length_map]
  rw [hc]
  grind only

theorem negativeNegateProgram_slots_le (n start : Nat) (target dirty : List Wire) (modulus : List Bool)
    (q c r t f : Wire) (hd : target.length=dirty.length) (hk : modulus.length=target.length)
    (hpos : 0<target.length) :
    (negativeNegateProgram n start target dirty modulus q c r t f).2.gateSlots ≤ 103*target.length+4 := by
  have h := modularNegateProgram_slots_le n start target dirty modulus q c r t f hd hk hpos
  simp only [negativeNegateProgram,prependCompiled_slots,appendCompiled_slots,literalProgram_slots,
    List.length_cons,List.length_nil]
  omega

theorem yNegateProgram_slots_le (start : Nat) : (yNegateProgram start).2.gateSlots ≤ 26372 := by
  have h := negativeNegateProgram_slots_le 32768 start (List.range' 580 256) (List.range' 7 256)
    (constantBits 256 ShorECDLP.p) 854 559 560 561 558
    (by simp only [List.length_range']) (by rw [constantBits_length,List.length_range']) (by simp only [List.length_range']; decide)
  change (yNegateProgram start).2.gateSlots ≤ _ at h
  simpa only [List.length_range'] using h

theorem uncontrolledCompareProgram_slots_le (n start : Nat) (input dirty : List Wire) (threshold : Nat)
    (c r t f : Wire) (hd : input.length=dirty.length) :
    (uncontrolledCompareProgram n start input dirty threshold c r t f).2.gateSlots ≤ 25*input.length+1 := by
  simp only [uncontrolledCompareProgram,constantStraight_slots]
  exact compareGEProgram_slots_le n start input dirty threshold _ c r t f hd

theorem controlledAddCarry_length256 (bs as : List Wire) (q c f : Wire)
    (hb : bs.length=256) (ha : as.length=256) : (controlledAddCarry bs as q c f).length=1793 := by
  rw [circuit_length_primitive,controlledAddCarry256_primitive _ _ _ _ _ hb ha .done]
  rfl

theorem controlledCompareLT_length256 (bs as : List Wire) (q c f : Wire)
    (hb : bs.length=256) (ha : as.length=256) : (controlledCompareLT bs as q c f).length=2053 := by
  rw [circuit_length_primitive,controlledCompareLT256_primitive _ _ _ _ _ hb ha .done]
  rfl

attribute [local irreducible] uncontrolledCompareProgram

theorem modularAddProgram_slots256 (n start : Nat) (input acc : List Wire) (correction : List Bool)
    (p : Nat) (q c r t f : Wire) (hi : input.length=256) (ha : acc.length=256)
    (hk : correction.length=256) :
    (modularAddProgram n start input acc correction p q c r t f).2.gateSlots ≤ 16903 := by
  have ht (s : Nat) := uncontrolledCompareProgram_slots_le n s acc input p c r t f (ha.trans hi.symm)
  have hg (s : Nat) := gidneyProgram_slots_le n s acc (input.take (acc.length-1)) correction f c r t
    (by simp only [List.length_take,hi,ha]; decide) (hk.trans ha.symm)
  have hb := controlledAddCarry_length256 input acc q c f hi ha
  have hc := controlledCompareLT_length256 acc input q c f ha hi
  simp only [modularAddProgram,appendCompiled_slots,Straight.gateSlots_append,literalProgram_slots,hb,hc]
  simp only [ha] at ht hg
  grind only

theorem circuit_adjoint_length (gs : Circuit) : gs.adjoint.length=gs.length := by
  simp only [Circuit.adjoint,List.length_map,List.length_reverse]

theorem modularSubProgram_slots256 (n start : Nat) (input acc : List Wire) (bits : List Bool)
    (p : Nat) (q c r t f : Wire) (hi : input.length=256) (ha : acc.length=256)
    (hk : bits.length=256) :
    (modularSubProgram n start input acc bits p q c r t f).2.gateSlots ≤ 16903 := by
  have ht (s : Nat) := uncontrolledCompareProgram_slots_le n s acc input p c r t f (ha.trans hi.symm)
  have hg (s : Nat) := gidneyProgram_slots_le n s acc (input.take (acc.length-1)) bits f c r t
    (by simp only [List.length_take,hi,ha]; decide) (hk.trans ha.symm)
  have hb := controlledAddCarry_length256 input acc q c f hi ha
  have hc := controlledCompareLT_length256 acc input q c f ha hi
  simp only [modularSubProgram,appendCompiled_slots,prependCompiled_slots,literalProgram_slots,
    controlledSubCarry,circuit_adjoint_length,hb,hc]
  simp only [ha] at ht hg
  grind only

theorem doublingShift_length256 (acc : List Wire) (f : Wire) (ha : acc.length=256) :
    (doublingShift acc f).length=767 := by
  rw [circuit_length_primitive,doublingShift256_primitive _ _ ha .done]
  rfl

theorem modularDoubleProgram_slots256 (n start : Nat) (acc dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (ha : acc.length=256) (hd : dirty.length=256) (hk : bits.length=256) :
    (modularDoubleProgram n start acc dirty bits p c r t f).2.gateSlots ≤ 13825 := by
  cases acc with
  | nil => simp at ha
  | cons a rest =>
    have ht (s : Nat) := uncontrolledCompareProgram_slots_le n s (a::rest) dirty p c r t f (ha.trans hd.symm)
    have hg (s : Nat) := gidneyProgram_slots_le n s (a::rest) (dirty.take rest.length) bits f c r t
      (by simp only [List.length_take,List.length_cons] at ha ⊢; omega) (hk.trans ha.symm)
    have hb := doublingShift_length256 (a::rest) f ha
    simp only [modularDoubleProgram,appendCompiled_slots,prependCompiled_slots,literalProgram_slots,
      List.length_cons,List.length_nil,hb]
    simp only [ha] at ht hg
    grind only

theorem modularHalveProgram_slots256 (n start : Nat) (acc dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (ha : acc.length=256) (hd : dirty.length=256) (hk : bits.length=256) :
    (modularHalveProgram n start acc dirty bits p c r t f).2.gateSlots ≤ 13825 := by
  cases acc with
  | nil => simp at ha
  | cons a rest =>
    have ht (s : Nat) := uncontrolledCompareProgram_slots_le n s (a::rest) dirty p c r t f (ha.trans hd.symm)
    have hg (s : Nat) := gidneyProgram_slots_le n s (a::rest) (dirty.take rest.length) bits f c r t
      (by simp only [List.length_take,List.length_cons] at ha ⊢; omega) (hk.trans ha.symm)
    have hb := doublingShift_length256 (a::rest) f ha
    simp only [modularHalveProgram,appendCompiled_slots,prependCompiled_slots,literalProgram_slots,
      List.length_cons,List.length_nil,circuit_adjoint_length,hb]
    simp only [ha] at ht hg
    grind only

theorem compiledIf_slots {n start : Nat} (b : Prop) [Decidable b]
    (p q : (count : Nat) × Straight n start (start+count)) :
    (if b then p else q).2.gateSlots = if b then p.2.gateSlots else q.2.gateSlots := by
  by_cases hb : b
  · rw [if_pos hb,if_pos hb]
  · rw [if_neg hb,if_neg hb]

attribute [local irreducible] modularAddProgram modularSubProgram modularDoubleProgram modularHalveProgram

theorem hornerProgram_slots256 (n start : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (hi : input.length=256) (ha : acc.length=256) (hk : bits.length=256) :
    (hornerProgram n start controls input acc bits p c r t f).2.gateSlots ≤ 30728*controls.length := by
  induction controls generalizing start with
  | nil => exact Nat.zero_le _
  | cons q qs ih =>
    have hb := ih start
    have hadd (s : Nat) := modularAddProgram_slots256 n s input acc bits p q c r t f hi ha hk
    have hdbl (s : Nat) := modularDoubleProgram_slots256 n s acc input bits p f r t c ha hi hk
    by_cases hz : qs=[]
    · subst qs
      simp only [hornerProgram,appendCompiled_slots,Straight.gateSlots,List.length_cons,List.length_nil]
      grind only
    · rw [hornerProgram]
      simp only [appendCompiled_slots,compiledIf_slots,hz,ite_false,List.length_cons]
      grind only

theorem hornerInverseProgram_slots256 (n start : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (hi : input.length=256) (ha : acc.length=256) (hk : bits.length=256) :
    (hornerInverseProgram n start controls input acc bits p c r t f).2.gateSlots ≤ 30728*controls.length := by
  induction controls generalizing start with
  | nil => exact Nat.zero_le _
  | cons q qs ih =>
    have hsub (s : Nat) := modularSubProgram_slots256 n s input acc bits p q c r t f hi ha hk
    have hhalf (s : Nat) := modularHalveProgram_slots256 n s acc input bits p f r t c ha hi hk
    by_cases hz : qs=[]
    · subst qs
      simp only [hornerInverseProgram,appendCompiled_slots,compiledIf_slots,ite_true,Straight.gateSlots,List.length_cons,List.length_nil]
      grind only
    · rw [hornerInverseProgram]
      simp only [appendCompiled_slots,compiledIf_slots,hz,ite_false,List.length_cons]
      grind only

theorem squareAddProgram_slots256 (n start : Nat) (input acc : List Wire) (bits : List Bool)
    (p : Nat) (q copied c r t f : Wire) (hi : input.length=256) (ha : acc.length=256) (hk : bits.length=256) :
    (squareAddProgram n start input acc bits p q copied c r t f).2.gateSlots ≤ 16905 := by
  have h := modularAddProgram_slots256 n start input acc bits p copied c r t f hi ha hk
  simp only [squareAddProgram,prependCompiled_slots,appendCompiled_slots,literalProgram_slots,List.length_cons,List.length_nil]
  omega

theorem squareSubProgram_slots256 (n start : Nat) (input acc : List Wire) (bits : List Bool)
    (p : Nat) (q copied c r t f : Wire) (hi : input.length=256) (ha : acc.length=256) (hk : bits.length=256) :
    (squareSubProgram n start input acc bits p q copied c r t f).2.gateSlots ≤ 16905 := by
  have h := modularSubProgram_slots256 n start input acc bits p copied c r t f hi ha hk
  simp only [squareSubProgram,prependCompiled_slots,appendCompiled_slots,literalProgram_slots,List.length_cons,List.length_nil]
  omega

attribute [local irreducible] squareAddProgram squareSubProgram
theorem squareProgram_slots256 (n start : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (copied c r t f : Wire) (hi : input.length=256) (ha : acc.length=256) (hk : bits.length=256) :
    (squareProgram n start controls input acc bits p copied c r t f).2.gateSlots ≤ 30730*controls.length := by
  induction controls generalizing start with
  | nil => exact Nat.zero_le _
  | cons q qs ih =>
    have hb := ih start
    have hadd (s : Nat) := squareAddProgram_slots256 n s input acc bits p q copied c r t f hi ha hk
    have hdbl (s : Nat) := modularDoubleProgram_slots256 n s acc input bits p f r t c ha hi hk
    by_cases hz : qs=[]
    · subst qs
      simp only [squareProgram,appendCompiled_slots,Straight.gateSlots,List.length_cons,List.length_nil]
      grind only
    · rw [squareProgram]
      simp only [appendCompiled_slots,compiledIf_slots,hz,ite_false,List.length_cons]
      grind only

theorem squareInverseProgram_slots256 (n start : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (copied c r t f : Wire) (hi : input.length=256) (ha : acc.length=256) (hk : bits.length=256) :
    (squareInverseProgram n start controls input acc bits p copied c r t f).2.gateSlots ≤ 30730*controls.length := by
  induction controls generalizing start with
  | nil => exact Nat.zero_le _
  | cons q qs ih =>
    have hsub (s : Nat) := squareSubProgram_slots256 n s input acc bits p q copied c r t f hi ha hk
    have hhalf (s : Nat) := modularHalveProgram_slots256 n s acc input bits p f r t c ha hi hk
    by_cases hz : qs=[]
    · subst qs
      simp only [squareInverseProgram,appendCompiled_slots,compiledIf_slots,ite_true,Straight.gateSlots,List.length_cons,List.length_nil]
      grind only
    · rw [squareInverseProgram]
      simp only [appendCompiled_slots,compiledIf_slots,hz,ite_false,List.length_cons]
      grind only

attribute [local irreducible] squareProgram squareInverseProgram

theorem squareSubtractProgram_slots256 (n start : Nat) (x y acc : List Wire) (correction modulus : List Bool)
    (p : Nat) (q copied c r t f : Wire) (hx : x.length=256) (hy : y.length=256) (ha : acc.length=256)
    (hk : correction.length=256) (hm : modulus.length=256) :
    (squareSubtractProgram n start x y acc correction modulus p q copied c r t f).2.gateSlots ≤ 15750663 := by
  have hs (s : Nat) := squareProgram_slots256 n s y y acc correction p copied c r t f hy ha hk
  have hu (s : Nat) := squareInverseProgram_slots256 n s y y acc modulus p copied c r t f hy ha hm
  have hb (s : Nat) := modularSubProgram_slots256 n s acc x modulus p q copied f r c ha hx hm
  simp only [squareSubtractProgram,appendCompiled_slots]
  simp only [hy] at hs hu
  grind only

theorem fieldLeaf_slots {n : Nat} (row : Fin n) (field : PointField) (q : Wire) :
    (fieldLeaf row field q).length=256 := by
  simp only [fieldLeaf,lookupLeafGates,List.length_map,List.length_zip,fieldRefs,List.length_ofFn,List.length_range']
  rfl

theorem fieldLoadProgram_slots (field : PointField) (start : Nat) :
    (fieldLoadProgram field start).gateSlots ≤ 8716278 := by
  simp only [fieldLoadProgram,castFinish_gateSlots,lookupProgram_slots,fieldLoadOps]
  have h := unaryLookupOps_slots_le
    (fun l q => fieldLeaf (⟨l%32768,Nat.mod_lt _ (by decide)⟩ : Fin 32768) field q)
    256 (fun l q => (fieldLeaf_slots _ field q).le)
    (tableAddressTree pointLookupAddress 0 1) 836 pointLookupPath
  have hn := tableAddressTree_nodes pointLookupAddress 0 1
  change (tableAddressTree pointLookupAddress 0 1).internalNodes + 1 = 32768 at hn
  omega

theorem fieldLookupAddProgram_slots (field : PointField) (acc : List Wire) (start : Nat)
    (ha : acc.length=256) : (fieldLookupAddProgram field acc start).2.gateSlots ≤ 17449459 := by
  have h (s : Nat) := fieldLoadProgram_slots field s
  have ha' (s : Nat) := modularAddProgram_slots256 32768 s (List.range' 7 256) acc
    secp256k1ReductionConstantBits ShorECDLP.p 836 559 560 561 558
    (by simp only [List.length_range']) ha (by simp [secp256k1ReductionConstantBits])
  simp only [fieldLookupAddProgram,appendCompiled_slots]
  grind only

theorem signedFieldProgram_slots (field : PointField) (start : Nat) :
    (signedFieldProgram field start).2.gateSlots ≤ 17502203 := by
  have hy (s : Nat) := yNegateProgram_slots_le s
  have hf (s : Nat) := fieldLookupAddProgram_slots field (List.range' 580 256) s (by simp only [List.length_range'])
  simp only [signedFieldProgram,appendCompiled_slots]
  grind only

end ShorECDLP.Paper2607_13816.ChallengeMigration
