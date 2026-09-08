import ShorECDLP.Submission.«2607_13816».Arithmetic.CarryAdd
import ShorECDLP.Submission.«2607_13816».EEA.IntervalCleanup

/-!
# Carry-probe comparison

The quadratic modular-adder backend clears its reduction flag using a controlled comparison.
This module follows the pinned Cuccaro carry-probe implementation, preserving both operands
and returning its one scratch carry to zero.
-/

namespace ShorECDLP.Paper2607_13816

open Classical
set_option linter.unusedSimpArgs false

private def majorityPass : List Wire → List Wire → Wire → Circuit
  | b :: bs, a :: as, c => cuccaroMaj b a c ++ majorityPass bs as b
  | _, _, _ => []

private def carryProbe : List Wire → Wire → Wire
  | [], c => c
  | b :: bs, _ => carryProbe bs b

private def complementWord (ws : List Wire) : Circuit := ws.map Gate.X

/-- Controlled XOR comparison. The full carry chain is used also at width one instead of
the source's optional short one-bit optimization. The empty comparison is identity. -/
def controlledCompareLT (left right : List Wire) (control carry flag : Wire) : Circuit :=
  match left with
  | [] => []
  | _ :: _ =>
      complementWord right ++ [.X carry] ++ majorityPass left right carry ++
        [.X (carryProbe left carry), .CCX control (carryProbe left carry) flag,
          .X (carryProbe left carry)] ++
        (majorityPass left right carry).adjoint ++ [.X carry] ++ complementWord right

private theorem majorityPass_usesOnly (bs as : List Wire) (c : Wire) :
    PaperCircuitUsesOnly (c :: bs ++ as) (majorityPass bs as c) := by
  induction bs generalizing as c with
  | nil => simp [majorityPass, PaperCircuitUsesOnly]
  | cons b bs ih =>
      cases as with
      | nil => simp [majorityPass, PaperCircuitUsesOnly]
      | cons a as =>
          apply PaperCircuitUsesOnly.append
          · simp [cuccaroMaj, PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires]
          · apply (ih as b).mono
            intro w hw
            simp only [List.cons_append, List.mem_cons, List.mem_append] at hw ⊢
            rcases hw with h | h | h <;> simp_all

private theorem majorityPass_child_layout (bs as : List Wire) (b a c : Wire)
    (hnd : (c :: (b :: bs) ++ a :: as).Nodup) :
    (b :: bs ++ as).Nodup := by
  apply List.Nodup.sublist (l₂ := c :: (b :: bs) ++ a :: as) ?_ hnd
  simpa only [List.cons_append] using
    List.Sublist.cons c (List.Sublist.cons₂ b
      ((List.Sublist.refl bs).append (List.sublist_cons_self a as)))

private theorem majorityPass_head_layout (bs as : List Wire) (b a c : Wire)
    (hnd : (c :: (b :: bs) ++ a :: as).Nodup) :
    [b,a,c].Nodup := by
  have hc := (List.nodup_cons.mp hnd).1
  have hp := List.nodup_append.mp (List.nodup_cons.mp hnd).2
  have hba : b ≠ a := by intro h; exact hp.2.2 b (by simp) a (by simp) h
  have hbc : b ≠ c := by intro h; exact hc (by simp [← h])
  have hac : a ≠ c := by intro h; exact hc (by simp [← h])
  simp [hba,hbc,hac]

private theorem majorityPass_wellFormed (bs as : List Wire) (c : Wire)
    (hlen : bs.length = as.length) (hnd : (c :: bs ++ as).Nodup) :
    CircuitWellFormed (majorityPass bs as c) := by
  induction bs generalizing as c with
  | nil => simp [majorityPass]
  | cons b bs ih =>
      cases as with
      | nil => simp at hlen
      | cons a as =>
          have hhead := majorityPass_head_layout bs as b a c hnd
          have hchild := majorityPass_child_layout bs as b a c hnd
          rw [majorityPass, circuitWellFormed_append]
          refine ⟨?_, ih as b (by simpa using hlen) hchild⟩
          simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or,
            not_false_eq_true, and_true] at hhead
          simp_all [cuccaroMaj, CircuitWellFormed, Gate.WellFormed, ne_comm]

private theorem majority_cell_state (b a c : Wire) (s : BasisState)
    (hnd : [b,a,c].Nodup) :
    run (cuccaroMaj b a c) s =
      upd (upd (upd s a (Bool.xor (s a) (s b))) c (Bool.xor (s c) (s b))) b
        (cuccaroCarry (s b) (s a) (s c)) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or,
    not_false_eq_true, List.nodup_nil, and_true] at hnd
  rcases hnd with ⟨⟨hba,hbc⟩,hac⟩
  funext w
  simp [cuccaroMaj, run_cons, run_nil, applyGate, upd, hba,hbc,hac,
    Ne.symm hba, Ne.symm hbc, Ne.symm hac, cuccaroCarry]

private theorem majorityPass_probe (bs as : List Wire) (c : Wire) (s : BasisState)
    (hlen : bs.length = as.length) (hnd : (c :: bs ++ as).Nodup) :
    run (majorityPass bs as c) s (carryProbe bs c) =
      carryAddOverflow (s c) (wireValues bs s) (wireValues as s) := by
  induction bs generalizing as c s with
  | nil =>
      have : as = [] := List.length_eq_zero_iff.mp hlen.symm
      subst as
      rfl
  | cons b bs ih =>
      cases as with
      | nil => simp at hlen
      | cons a as =>
          have hhead := majorityPass_head_layout bs as b a c hnd
          have hchild := majorityPass_child_layout bs as b a c hnd
          have hcell := majority_cell_state b a c s hhead
          have hc := (List.nodup_cons.mp hnd).1
          have hp := List.nodup_append.mp (List.nodup_cons.mp hnd).2
          have hbbs := (List.nodup_cons.mp hp.1).1
          have haas := (List.nodup_cons.mp hp.2.1).1
          have habs : a ∉ bs := by intro h; exact hp.2.2 a (by simp [h]) a (by simp) rfl
          have hbas : b ∉ as := by intro h; exact hp.2.2 b (by simp) b (by simp [h]) rfl
          have hcbs : c ∉ bs := by intro h; exact hc (by simp [h])
          have hcas : c ∉ as := by intro h; exact hc (by simp [h])
          let first := run (cuccaroMaj b a c) s
          have first_b : first b = cuccaroCarry (s b) (s a) (s c) := by
            dsimp [first]; rw [hcell]; simp [upd]
          have first_bs : wireValues bs first = wireValues bs s := by
            apply List.map_congr_left
            intro w hw
            dsimp [first]; rw [hcell]
            have hwb : w ≠ b := fun h => hbbs (h ▸ hw)
            have hwa : w ≠ a := fun h => habs (h ▸ hw)
            have hwc : w ≠ c := fun h => hcbs (h ▸ hw)
            simp [upd,hwb,hwa,hwc]
          have first_as : wireValues as first = wireValues as s := by
            apply List.map_congr_left
            intro w hw
            dsimp [first]; rw [hcell]
            have hwb : w ≠ b := fun h => hbas (h ▸ hw)
            have hwa : w ≠ a := fun h => haas (h ▸ hw)
            have hwc : w ≠ c := fun h => hcas (h ▸ hw)
            simp [upd,hwb,hwa,hwc]
          rw [majorityPass, run_append]
          change run (majorityPass bs as b) first (carryProbe bs b) = _
          rw [ih as b first (by simpa using hlen) hchild, first_b, first_bs, first_as]
          rfl

private theorem majorityPass_counts (bs as : List Wire) (c : Wire)
    (hlen : bs.length = as.length) :
    eeaToffoliCount (majorityPass bs as c) = bs.length ∧
      eeaCnotCount (majorityPass bs as c) = 2 * bs.length ∧
      tCount (majorityPass bs as c) = 7 * bs.length := by
  induction bs generalizing as c with
  | nil => simp [majorityPass, eeaToffoliCount,eeaCnotCount,tCount]
  | cons b bs ih =>
      cases as with
      | nil => simp at hlen
      | cons a as =>
          have hr := ih as b (by simpa using hlen)
          simp only [majorityPass, eeaToffoliCount_append, eeaCnotCount_append, tCount_append]
          rw [hr.1,hr.2.1,hr.2.2]
          simp [cuccaroMaj,eeaToffoliCount,eeaCnotCount,tCount,tCost]
          omega


private theorem complementWord_state (ws : List Wire) (s : BasisState) (hnd : ws.Nodup) :
    run (complementWord ws) s = fun w => if w ∈ ws then !s w else s w := by
  induction ws generalizing s with
  | nil => rfl
  | cons a as ih =>
      have ha := (List.nodup_cons.mp hnd).1
      have ht := (List.nodup_cons.mp hnd).2
      change run (Gate.X a :: complementWord as) s = _
      rw [run_cons, ih _ ht]
      funext w
      by_cases hwa : w = a
      · subst w; simp [ha,applyGate,upd]
      · simp [hwa,applyGate,upd]

private theorem complementWord_usesOnly (ws : List Wire) :
    PaperCircuitUsesOnly ws (complementWord ws) := by
  intro g hg w hw
  simp only [complementWord, List.mem_map] at hg
  obtain ⟨v,hv,rfl⟩ := hg
  have heq : w = v := by simpa [gateWires] using hw
  simpa [heq] using hv

private theorem complementWord_wellFormed (ws : List Wire) :
    CircuitWellFormed (complementWord ws) := by
  simp [complementWord,CircuitWellFormed,Gate.WellFormed]

private theorem complementWord_adjoint_run (ws : List Wire) (hnd : ws.Nodup) (s : BasisState) :
    run (complementWord ws).adjoint s = run (complementWord ws) s := by
  have htwice : run (complementWord ws) (run (complementWord ws) s) = s := by
    rw [complementWord_state ws _ hnd, complementWord_state ws s hnd]
    funext w
    by_cases hw : w ∈ ws <;> simp [hw]
  have h := run_adjoint_run_classical (complementWord ws)
    (complementWord_wellFormed ws) (run (complementWord ws) s)
  rw [htwice] at h
  exact h

private theorem usesOnly_run_upd {support : List Wire} {circuit : Circuit}
    (huses : PaperCircuitUsesOnly support circuit) (s : BasisState) (f : Wire)
    (value : Bool) (hf : f ∉ support) :
    run circuit (upd s f value) = upd (run circuit s) f value := by
  funext w
  by_cases hwf : w = f
  · subst w
    rw [huses.preservesOutside _ hf]
    simp [upd]
  · by_cases hws : w ∈ support
    · have heq := huses.run_congrOn (upd s f value) s (by
        intro v hv
        have hvf : v ≠ f := fun h => hf (h ▸ hv)
        simp [upd,hvf]) w hws
      simpa [upd,hwf] using heq
    · rw [huses.preservesOutside _ hws]
      simp [upd,hwf,huses.preservesOutside s hws]

private theorem probePulse_state (q p f : Wire) (s : BasisState)
    (hqp : q ≠ p) (_hqf : q ≠ f) (hpf : p ≠ f) :
    run [.X p, .CCX q p f, .X p] s =
      upd s f (Bool.xor (s f) (s q && !s p)) := by
  funext w
  simp [run_cons,run_nil,applyGate,upd,hqp,_hqf,hpf,
    Ne.symm hqp,Ne.symm _hqf,Ne.symm hpf]
  by_cases hwp : w = p <;> by_cases hwf : w = f <;> simp_all

private theorem probeSandwich_state (compute : Circuit) (support : List Wire)
    (q p f : Wire) (s : BasisState)
    (huses : PaperCircuitUsesOnly support compute) (hwell : CircuitWellFormed compute)
    (hq : q ∉ support) (hf : f ∉ support) (hp : p ∈ support) (hqf : q ≠ f) :
    run (compute ++ [.X p,.CCX q p f,.X p] ++ compute.adjoint) s =
      upd s f (Bool.xor (s f) (s q && !(run compute s p))) := by
  have hqp : q ≠ p := fun h => hq (h ▸ hp)
  have hpf : p ≠ f := fun h => hf (h ▸ hp)
  rw [run_append,run_append,probePulse_state q p f _ hqp hqf hpf]
  rw [usesOnly_run_upd huses.adjoint _ f _ hf,
    run_adjoint_run_classical compute hwell s,
    huses.preservesOutside s hf,huses.preservesOutside s hq]

private theorem carryProbe_mem (bs : List Wire) (c : Wire) : carryProbe bs c ∈ c :: bs := by
  induction bs generalizing c with
  | nil => simp [carryProbe]
  | cons b bs ih =>
      have h := ih b
      simp only [carryProbe,List.mem_cons] at h ⊢
      exact Or.inr h

private theorem compareOverflow_value (bs as : List Bool) (hlen : bs.length = as.length) :
    Bool.not (carryAddOverflow true bs (as.map Bool.not)) =
      decide (boolWordToNat bs < boolWordToNat as) := by
  have hover := carryAddBits_value true bs (as.map Bool.not) (by simpa using hlen)
  have hlow := boolWordToNat_lt_pow_two (cuccaroAddBits true bs (as.map Bool.not))
  have hlen' := cuccaroAddBits_length true bs (as.map Bool.not) (by simpa using hlen)
  rw [hlen'] at hlow
  have hnot := boolWordToNat_map_not_add as
  rw [← hlen] at hnot
  have hb := boolWordToNat_lt_pow_two bs
  have ha := boolWordToNat_lt_pow_two as
  rw [← hlen] at ha
  cases hcarry : carryAddOverflow true bs (as.map Bool.not) <;>
    simp only [hcarry,Bool.toNat_true,Bool.toNat_false,Nat.mul_zero,Nat.mul_one] at hover
  · apply Eq.symm
    apply decide_eq_true
    omega
  · apply Eq.symm
    apply decide_eq_false
    omega

private def compareCompute (bs as : List Wire) (c : Wire) : Circuit :=
  complementWord as ++ [.X c] ++ majorityPass bs as c

private theorem compareCompute_usesOnly (bs as : List Wire) (c : Wire) :
    PaperCircuitUsesOnly (c :: bs ++ as) (compareCompute bs as c) := by
  apply PaperCircuitUsesOnly.append
  · apply PaperCircuitUsesOnly.append
    · exact (complementWord_usesOnly as).mono (by intro w hw; simp [hw])
    · simp [PaperCircuitUsesOnly,PaperGateUsesOnly,gateWires]
  · exact majorityPass_usesOnly bs as c

private theorem compareCompute_wellFormed (bs as : List Wire) (c : Wire)
    (hlen : bs.length = as.length) (hnd : (c :: bs ++ as).Nodup) :
    CircuitWellFormed (compareCompute bs as c) := by
  have hflip := complementWord_wellFormed as
  have hmaj := majorityPass_wellFormed bs as c hlen hnd
  intro g hg
  simp only [compareCompute,List.mem_append,List.mem_singleton] at hg
  rcases hg with (hg | rfl) | hg
  · exact hflip g hg
  · trivial
  · exact hmaj g hg

private theorem compareCompute_probe (bs as : List Wire) (c : Wire) (s : BasisState)
    (hlen : bs.length = as.length) (hnd : (c :: bs ++ as).Nodup) (hc : s c = false) :
    Bool.not (run (compareCompute bs as c) s (carryProbe bs c)) =
      decide (boolWordToNat (wireValues bs s) < boolWordToNat (wireValues as s)) := by
  have hca : c ∉ as := by
    intro hw; exact (List.nodup_cons.mp hnd).1 (by simp [hw])
  have hcb : c ∉ bs := by
    intro hw; exact (List.nodup_cons.mp hnd).1 (by simp [hw])
  have hparts := List.nodup_append.mp (List.nodup_cons.mp hnd).2
  let start := run (complementWord as ++ [.X c]) s
  have hstart : start = upd (fun w => if w ∈ as then !s w else s w) c true := by
    simp [start,run_append,complementWord_state as s hparts.2.1,run_cons,run_nil,
      applyGate,hca,hc]
  have hcarry : start c = true := by rw [hstart]; simp [upd]
  have hleft : wireValues bs start = wireValues bs s := by
    apply List.map_congr_left
    intro w hw
    have hwc : w ≠ c := fun he => hcb (he ▸ hw)
    have hwa : w ∉ as := fun ha => hparts.2.2 w hw w ha rfl
    simp [hstart,upd,hwc,hwa]
  have hright : wireValues as start = (wireValues as s).map Bool.not := by
    simp only [wireValues,List.map_map]
    apply List.map_congr_left
    intro w hw
    have hwc : w ≠ c := fun he => hca (he ▸ hw)
    simp [hstart,upd,hwc,hw]
  rw [compareCompute,run_append]
  change Bool.not (run (majorityPass bs as c) start (carryProbe bs c)) = _
  rw [majorityPass_probe bs as c start hlen hnd,hcarry,hleft,hright]
  exact compareOverflow_value _ _ (by simpa [wireValues] using hlen)

private theorem controlledCompareLT_sandwich (b : Wire) (bs as : List Wire)
    (q c f : Wire) (s : BasisState) (ha : as.Nodup) :
    run (controlledCompareLT (b :: bs) as q c f) s =
      run (compareCompute (b :: bs) as c ++
        [.X (carryProbe (b :: bs) c),.CCX q (carryProbe (b :: bs) c) f,
          .X (carryProbe (b :: bs) c)] ++ (compareCompute (b :: bs) as c).adjoint) s := by
  simp only [controlledCompareLT,compareCompute,circuit_adjoint_append,run_append]
  simp only [Circuit.adjoint,List.reverse_cons,List.reverse_nil,List.nil_append,
    List.map_append,List.map_cons,List.map_nil,Gate.adjoint]
  exact (complementWord_adjoint_run as ha _).symm

/-- Comparison XORs the controlled unsigned less-than result into an arbitrary flag.
Both operand words and every other wire, including the clean carry, are restored. -/
theorem controlledCompareLT_correct (left right : List Wire) (control carry flag : Wire)
    (s : BasisState) (hlen : left.length = right.length)
    (hnd : (control :: carry :: flag :: left ++ right).Nodup) (hc : s carry = false) :
    run (controlledCompareLT left right control carry flag) s =
      upd s flag (Bool.xor (s flag) (s control &&
        decide (boolWordToNat (wireValues left s) < boolWordToNat (wireValues right s)))) := by
  have hq := (List.nodup_cons.mp hnd).1
  have htail := (List.nodup_cons.mp hnd).2
  have hcf := (List.nodup_cons.mp htail).1
  have htail' := (List.nodup_cons.mp htail).2
  have hf := (List.nodup_cons.mp htail').1
  have hdata := (List.nodup_cons.mp htail').2
  have hlayout : (carry :: left ++ right).Nodup := by
    apply List.nodup_cons.mpr
    exact ⟨by intro hw; apply hcf; change carry ∈ flag :: (left ++ right); exact List.mem_cons_of_mem _ hw,hdata⟩
  cases left with
  | nil =>
    have hr : right = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
    subst right
    simp only [controlledCompareLT,run_nil,wireValues,List.map_nil,boolWordToNat]
    funext w
    by_cases hw : w = flag <;> simp [upd,hw]
  | cons b bs =>
    rw [controlledCompareLT_sandwich b bs right control carry flag s
      (List.nodup_append.mp hdata).2.1]
    rw [probeSandwich_state _ (carry :: (b :: bs) ++ right) control _ flag s
      (compareCompute_usesOnly _ _ _) (compareCompute_wellFormed _ _ _ hlen hlayout)
      (by intro hw; apply hq
          change control ∈ carry :: flag :: ((b :: bs) ++ right)
          change control ∈ carry :: ((b :: bs) ++ right) at hw
          simp only [List.mem_cons] at hw ⊢
          tauto)
      (by intro hw; simp only [List.cons_append,List.mem_cons] at hw; rcases hw with h | h
          · exact hcf (by simp [h])
          · apply hf; change flag ∈ b :: (bs ++ right); exact List.mem_cons.mpr h)
      (by have hm := carryProbe_mem (b :: bs) carry
          simp only [List.cons_append,List.mem_cons,List.mem_append] at hm ⊢
          tauto)
      (by intro h; exact hq (by simp [h]))]
    rw [compareCompute_probe _ _ _ s hlen hlayout hc]

/-- Repeating the comparator restores the full state, including an arbitrary flag. -/
theorem controlledCompareLT_involutive (left right : List Wire) (q c f : Wire)
    (s : BasisState) (hlen : left.length = right.length)
    (hnd : (q :: c :: f :: left ++ right).Nodup) (hc : s c = false) :
    run (controlledCompareLT left right q c f)
      (run (controlledCompareLT left right q c f) s) = s := by
  have hq := (List.nodup_cons.mp hnd).1
  have hcf := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
  have hf := (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2).1
  have hqf : q ≠ f := by intro h; exact hq (by simp [h])
  have hcf' : c ≠ f := by intro h; exact hcf (by simp [h])
  have hword (ws : List Wire) (hw : ∀ w ∈ ws, w ≠ f) (b : Bool) :
      wireValues ws (upd s f b) = wireValues ws s := by
    apply List.map_congr_left
    intro w hm
    simp [upd,hw w hm]
  have hl : ∀ w ∈ left, w ≠ f := by
    intro w hw he; subst w; exact hf (List.mem_append_left _ hw)
  have hr : ∀ w ∈ right, w ≠ f := by
    intro w hw he; subst w; exact hf (List.mem_append_right _ hw)
  rw [controlledCompareLT_correct left right q c f s hlen hnd hc]
  rw [controlledCompareLT_correct left right q c f _ hlen hnd (by simp [upd,hcf',hc])]
  rw [hword left hl,hword right hr]
  funext w
  by_cases hw : w = f <;>
    simp [upd,hw,hqf,Bool.xor_assoc]

private theorem majorityPass_HPFree (bs as : List Wire) (c : Wire) :
    HPFree (majorityPass bs as c) := by
  induction bs generalizing as c with
  | nil => simp [majorityPass]
  | cons b bs ih => cases as <;> simp [majorityPass,cuccaroMaj,ih]

private theorem majorityPass_xCount (bs as : List Wire) (c : Wire) :
    eeaXCount (majorityPass bs as c) = 0 := by
  induction bs generalizing as c with
  | nil => rfl
  | cons b bs ih =>
    cases as with
    | nil => rfl
    | cons a as => rw [majorityPass,eeaXCount_append,ih]; rfl

private theorem complementWord_counts (as : List Wire) :
    eeaToffoliCount (complementWord as) = 0 ∧
      eeaCnotCount (complementWord as) = 0 ∧
      eeaXCount (complementWord as) = as.length ∧
      tCount (complementWord as) = 0 := by
  induction as with
  | nil => simp [complementWord,eeaToffoliCount,eeaCnotCount,eeaXCount,tCount]
  | cons a as ih =>
    simp [complementWord,eeaToffoliCount,eeaCnotCount,eeaXCount,tCount,tCost] at *
    omega

/-- Exact source-stream gate counts for every nonempty equal-width comparator. -/
theorem controlledCompareLT_counts (b : Wire) (bs right : List Wire) (q c f : Wire)
    (hlen : (b :: bs).length = right.length) :
    eeaToffoliCount (controlledCompareLT (b :: bs) right q c f) = 2 * (bs.length + 1) + 1 ∧
      eeaCnotCount (controlledCompareLT (b :: bs) right q c f) = 4 * (bs.length + 1) ∧
      eeaXCount (controlledCompareLT (b :: bs) right q c f) = 2 * (bs.length + 1) + 4 ∧
      tCount (controlledCompareLT (b :: bs) right q c f) = 7 * (2 * (bs.length + 1) + 1) := by
  have hm := majorityPass_counts (b :: bs) right c hlen
  have hx := majorityPass_xCount (b :: bs) right c
  have hf := complementWord_counts right
  simp only [controlledCompareLT,eeaToffoliCount_append,eeaCnotCount_append,
    eeaXCount_append,tCount_append,eeaToffoliCount_adjoint,eeaCnotCount_adjoint,
    eeaXCount_adjoint,tCount_adjoint,hm.1,hm.2.1,hm.2.2,hx,hf.1,hf.2.1,hf.2.2.1,hf.2.2.2]
  simp only [List.length_cons] at hlen ⊢
  simp [eeaToffoliCount,eeaCnotCount,eeaXCount,tCount,tCost]
  omega

private theorem compare_adjoint_mem_wires (circuit : Circuit) (w : Wire) :
    w ∈ circuitWires circuit.adjoint ↔ w ∈ circuitWires circuit := by
  induction circuit with
  | nil => simp [circuitWires]
  | cons gate circuit ih =>
    rw [circuit_adjoint_cons]
    simp only [circuitWires,List.flatMap_append,List.mem_append,List.flatMap_cons,
      List.flatMap_nil,List.append_nil] at *
    cases gate <;> simp_all [gateWires,Gate.adjoint,or_comm]

private theorem majorityPass_mem_wires (b : Wire) (bs as : List Wire) (c w : Wire)
    (hlen : (b :: bs).length = as.length) :
    w ∈ circuitWires (majorityPass (b :: bs) as c) ↔ w ∈ c :: (b :: bs) ++ as := by
  induction bs generalizing b as c with
  | nil =>
    cases as with
    | nil => simp at hlen
    | cons a as =>
      have he : as = [] := by simpa using hlen.symm
      subst as
      simp [majorityPass,cuccaroMaj,circuitWires,gateWires,or_comm,or_left_comm,or_assoc]
  | cons b' bs ih =>
    cases as with
    | nil => simp at hlen
    | cons a as =>
      have htail : (b' :: bs).length = as.length := by simpa using hlen
      simp only [majorityPass,circuitWires,List.flatMap_append,List.mem_append]
      change w ∈ circuitWires (cuccaroMaj b a c) ∨
        w ∈ circuitWires (majorityPass (b' :: bs) as b) ↔ _
      rw [ih b' as b htail]
      simp [cuccaroMaj,circuitWires,gateWires,or_assoc,or_comm,or_left_comm]

theorem controlledCompareLT_wires (b : Wire) (bs right : List Wire) (q c f w : Wire)
    (hlen : (b :: bs).length = right.length) :
    w ∈ circuitWires (controlledCompareLT (b :: bs) right q c f) ↔
      w ∈ q :: c :: f :: (b :: bs) ++ right := by
  have hm := majorityPass_mem_wires b bs right c w hlen
  have hp := carryProbe_mem (b :: bs) c
  have hflip : w ∈ circuitWires (complementWord right) ↔ w ∈ right := by
    simp [complementWord,circuitWires,gateWires]
  simp only [controlledCompareLT,circuitWires,List.flatMap_append,List.mem_append]
  change (((((w ∈ circuitWires (complementWord right) ∨ w ∈ circuitWires [.X c]) ∨
    w ∈ circuitWires (majorityPass (b :: bs) right c)) ∨
    w ∈ circuitWires [.X (carryProbe (b :: bs) c),.CCX q (carryProbe (b :: bs) c) f,
      .X (carryProbe (b :: bs) c)]) ∨
    w ∈ circuitWires (majorityPass (b :: bs) right c).adjoint) ∨
    w ∈ circuitWires [.X c]) ∨ w ∈ circuitWires (complementWord right) ↔ _
  rw [compare_adjoint_mem_wires,hm,hflip]
  simp only [circuitWires,gateWires,List.flatMap_cons,List.flatMap_nil,List.mem_append,
    List.mem_cons,List.not_mem_nil] at *
  constructor
  · intro h
    by_cases he : w = carryProbe (b :: bs) c
    · subst w; aesop
    · aesop
  · aesop

/-- Exact distinct-wire count for the actual nonempty comparator stream. -/
theorem controlledCompareLT_qubitCount (b : Wire) (bs right : List Wire) (q c f : Wire)
    (hlen : (b :: bs).length = right.length)
    (hnd : (q :: c :: f :: (b :: bs) ++ right).Nodup) :
    qubitCount (controlledCompareLT (b :: bs) right q c f) = 2 * (bs.length + 1) + 3 := by
  have heq : (circuitWires (controlledCompareLT (b :: bs) right q c f)).dedup.toFinset =
      (q :: c :: f :: (b :: bs) ++ right).toFinset := by
    ext w
    simpa using controlledCompareLT_wires b bs right q c f w hlen
  have hc := congrArg Finset.card heq
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _),List.toFinset_card_of_nodup hnd] at hc
  simpa [qubitCount,← hlen,Nat.two_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hc

private theorem compare_hpFree_adjoint {circuit : Circuit} (h : HPFree circuit) :
    HPFree circuit.adjoint := by
  induction circuit with
  | nil => simp
  | cons g circuit ih =>
    have hp := (hpFree_cons g circuit).mp h
    rw [circuit_adjoint_cons,hpFree_append]
    refine ⟨ih hp.2,?_⟩
    cases g <;> simp_all [Gate.adjoint]

@[simp] theorem controlledCompareLT_HPFree (left right : List Wire) (q c f : Wire) :
    HPFree (controlledCompareLT left right q c f) := by
  cases left with
  | nil => simp [controlledCompareLT]
  | cons b bs =>
    have hm := majorityPass_HPFree (b :: bs) right c
    have ha := compare_hpFree_adjoint hm
    have hf : HPFree (complementWord right) := by
      simp [complementWord,HPFree]
    simp [controlledCompareLT,hm,ha,hf]

theorem controlledCompareLT_wellFormed (left right : List Wire) (q c f : Wire)
    (hlen : left.length = right.length) (hnd : (q :: c :: f :: left ++ right).Nodup) :
    CircuitWellFormed (controlledCompareLT left right q c f) := by
  have hq := (List.nodup_cons.mp hnd).1
  have ht := (List.nodup_cons.mp hnd).2
  have hc := (List.nodup_cons.mp ht).1
  have ht' := (List.nodup_cons.mp ht).2
  have hf := (List.nodup_cons.mp ht').1
  have hd := (List.nodup_cons.mp ht').2
  have hlayout : (c :: left ++ right).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,hd⟩
    intro hw; apply hc; change c ∈ f :: (left ++ right)
    exact List.mem_cons_of_mem _ hw
  have hm := majorityPass_wellFormed left right c hlen hlayout
  have ha := (circuitWellFormed_adjoint _).2 hm
  have hp := carryProbe_mem left c
  have hqp : q ≠ carryProbe left c := by
    intro he; apply hq
    change q ∈ c :: f :: (left ++ right)
    simp only [List.mem_cons,List.mem_append] at hp ⊢
    subst q; tauto
  have hpf : carryProbe left c ≠ f := by
    intro he
    simp only [List.mem_cons] at hp
    rcases hp with hp | hp
    · apply hc; change c ∈ f :: (left ++ right); exact List.mem_cons.mpr (Or.inl (hp.symm.trans he))
    · apply hf; change f ∈ left ++ right; simp [← he,hp]
  have hqf : q ≠ f := by
    intro he; apply hq; change q ∈ c :: f :: (left ++ right); simp [he]
  cases left with
  | nil => simp [controlledCompareLT,CircuitWellFormed]
  | cons b bs =>
    intro g hg
    simp only [controlledCompareLT,List.mem_append,List.mem_cons,List.not_mem_nil] at hg
    rcases hg with (((((hg | (rfl | h)) | hg) | (rfl | rfl | rfl | h)) | hg) |
      (rfl | h)) | hg
    · exact complementWord_wellFormed right g hg
    · trivial
    · contradiction
    · exact hm g hg
    · trivial
    · exact ⟨hqp,hqf,hpf⟩
    · trivial
    · contradiction
    · exact ha g hg
    · trivial
    · contradiction
    · exact complementWord_wellFormed right g hg

/-- Concrete 256-bit comparator: control 0, clean carry 1, XOR result flag 2,
left word 3–258 and right word 259–514. -/
def secp256k1ControlledCompareLT : Circuit :=
  controlledCompareLT (List.range' 3 256) (List.range' 259 256) 0 1 2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem secp256k1Compare_layout :
    (0 :: 1 :: 2 :: List.range' 3 256 ++ List.range' 259 256).Nodup := by decide

/-- Human-readable same-circuit certificate: the flag receives the controlled unsigned
comparison; both operands, control, carry and all other wires are preserved. This exact
256-bit circuit has 513 Toffolis, 1,024 CNOTs, 516 X gates, 3,591 coherent T gates and
515 distinct wires. The initial flag is arbitrary; only the carry must start clean. -/
theorem secp256k1ControlledCompareLT_correct_resources (s : BasisState) (hcarry : s 1 = false) :
    let after := run secp256k1ControlledCompareLT s
    let left := boolWordToNat (wireValues (List.range' 3 256) s)
    let right := boolWordToNat (wireValues (List.range' 259 256) s)
    after 2 = Bool.xor (s 2) (s 0 && decide (left < right)) ∧
      (∀ w, w ≠ 2 → after w = s w) ∧
      CircuitWellFormed secp256k1ControlledCompareLT ∧
      HPFree secp256k1ControlledCompareLT ∧
      eeaToffoliCount secp256k1ControlledCompareLT = 513 ∧
      eeaCnotCount secp256k1ControlledCompareLT = 1024 ∧
      eeaXCount secp256k1ControlledCompareLT = 516 ∧
      tCount secp256k1ControlledCompareLT = 3591 ∧
      qubitCount secp256k1ControlledCompareLT = 515 := by
  have hlen : (List.range' 3 256).length = (List.range' 259 256).length := by simp
  have hsem := controlledCompareLT_correct _ _ 0 1 2 s hlen secp256k1Compare_layout hcarry
  have hcounts := controlledCompareLT_counts 3 (List.range' 4 255) (List.range' 259 256)
    0 1 2 (by simp)
  have hqubits := controlledCompareLT_qubitCount 3 (List.range' 4 255) (List.range' 259 256)
    0 1 2 (by simp) secp256k1Compare_layout
  dsimp only
  refine ⟨?_,?_,controlledCompareLT_wellFormed _ _ _ _ _ hlen secp256k1Compare_layout,
    controlledCompareLT_HPFree _ _ _ _ _,?_,?_,?_,?_,?_⟩
  · change run (controlledCompareLT _ _ 0 1 2) s 2 = _
    rw [hsem]; simp [upd]
  · intro w hw
    change run (controlledCompareLT _ _ 0 1 2) s w = _
    rw [hsem]; simp [upd,hw]
  · change eeaToffoliCount (controlledCompareLT (3 :: List.range' 4 255) _ 0 1 2) = _
    simpa only [List.length_range'] using hcounts.1
  · change eeaCnotCount (controlledCompareLT (3 :: List.range' 4 255) _ 0 1 2) = _
    simpa only [List.length_range'] using hcounts.2.1
  · change eeaXCount (controlledCompareLT (3 :: List.range' 4 255) _ 0 1 2) = _
    simpa only [List.length_range'] using hcounts.2.2.1
  · change tCount (controlledCompareLT (3 :: List.range' 4 255) _ 0 1 2) = _
    simpa only [List.length_range'] using hcounts.2.2.2
  · change qubitCount (controlledCompareLT (3 :: List.range' 4 255) _ 0 1 2) = _
    simpa only [List.length_range'] using hqubits

end ShorECDLP.Paper2607_13816
