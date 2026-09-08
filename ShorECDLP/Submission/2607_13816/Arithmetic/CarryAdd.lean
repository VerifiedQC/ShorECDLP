import ShorECDLP.Submission.«2607_13816».EEA.WordNat
import Mathlib.Data.Finset.Card

/-!
# Controlled addition with a reusable carry

The two passes below follow `append_controlled_add_mod2_with_carry_flag` in the pinned
`quadratic_gidney_arithmetic.py` for widths at least two. The carry is shared across all
lanes; the unconditional XOR skeleton is undone even when the external control is false.
The uniform recurrence also handles width one correctly, unlike the source's special
one-bit branch, which toggles the output flag without consulting the target bit.
-/

namespace ShorECDLP.Paper2607_13816

open Classical

set_option linter.unusedSimpArgs false

/-- Forward cell of the Appendix-B controlled carry-output adder. -/
def carryAddMaj (addend target carry : Wire) : Circuit :=
  [.CX carry addend, .CX carry target, .CCX target addend carry]

/-- Reverse cell restores the carry and addend, and conditionally emits the sum bit. -/
def carryAddUma (control addend target carry : Wire) : Circuit :=
  [.CCX target addend carry, .CX carry target,
    .CCX control addend target, .CX carry addend]

/-- LSB-first recursive spelling of the pinned forward pass, controlled carry copy,
and descending reverse pass. Equal register lengths are required by correctness. -/
def controlledAddCarry : List Wire → List Wire → Wire → Wire → Wire → Circuit
  | [], [], control, carry, flag => [.CCX control carry flag]
  | addend :: addends, target :: targets, control, carry, flag =>
      carryAddMaj addend target carry ++
        controlledAddCarry addends targets control carry flag ++
          carryAddUma control addend target carry
  | _, _, _, _, _ => []

/-- Literal inverse circuit, including the output-carry XOR. -/
def controlledSubCarry (addends targets : List Wire) (control carry flag : Wire) : Circuit :=
  Circuit.adjoint (controlledAddCarry addends targets control carry flag)

private theorem run_carryAddMaj (b a c : Wire) (s : BasisState)
    (hba : b ≠ a) (hbc : b ≠ c) (hac : a ≠ c) :
    run (carryAddMaj b a c) s =
      upd (upd (upd s b (Bool.xor (s b) (s c))) a
        (Bool.xor (s a) (s c))) c (cuccaroCarry (s b) (s a) (s c)) := by
  funext w
  simp only [carryAddMaj, run_cons, run_nil, applyGate]
  simp [upd, hba, hbc, hac, Ne.symm hba, Ne.symm hbc, Ne.symm hac, cuccaroCarry]
  cases s b <;> cases s a <;> cases s c <;> simp

private theorem run_carryAddUma_prepared (q b a c : Wire) (s : BasisState)
    (control addend target carry : Bool)
    (_hqb : q ≠ b) (hqa : q ≠ a) (hqc : q ≠ c)
    (hba : b ≠ a) (hbc : b ≠ c) (hac : a ≠ c)
    (hq : s q = control)
    (hb : s b = Bool.xor addend carry)
    (ha : s a = Bool.xor target carry)
    (hc : s c = cuccaroCarry addend target carry) :
    run (carryAddUma q b a c) s =
      upd (upd (upd s c carry) a
        (if control then cuccaroSum addend target carry else target)) b addend := by
  funext w
  simp only [carryAddUma, run_cons, run_nil, applyGate]
  simp [upd, _hqb, hqa, hqc, hba, hbc, hac,
    Ne.symm _hqb, Ne.symm hqa, Ne.symm hqc,
    Ne.symm hba, Ne.symm hbc, Ne.symm hac, hq, hb, ha, hc,
    cuccaroCarry, cuccaroSum]
  by_cases hwB : w = b <;> by_cases hwA : w = a <;> by_cases hwC : w = c <;>
    cases control <;> cases addend <;> cases target <;> cases carry <;> simp_all

/-- Carry-out of the ordinary full-adder recurrence, before gating the flag update. -/
def carryAddOverflow : Bool → List Bool → List Bool → Bool
  | carry, [], [] => carry
  | carry, b :: bs, a :: as => carryAddOverflow (cuccaroCarry b a carry) bs as
  | carry, _, _ => carry

/-- Exact integer identity for the low word and carry-out. -/
theorem carryAddBits_value (carry : Bool) (bs as : List Bool)
    (hlen : bs.length = as.length) :
    boolWordToNat (cuccaroAddBits carry bs as) +
        2 ^ bs.length * (carryAddOverflow carry bs as).toNat =
      carry.toNat + boolWordToNat bs + boolWordToNat as := by
  induction bs generalizing carry as with
  | nil =>
      have : as = [] := List.length_eq_zero_iff.mp hlen.symm
      subst as
      simp [cuccaroAddBits, carryAddOverflow]
  | cons b bs ih =>
      cases as with
      | nil => simp at hlen
      | cons a as =>
          have htail : bs.length = as.length := by simpa using hlen
          have hrec := ih (cuccaroCarry b a carry) as htail
          have hcell : (cuccaroSum b a carry).toNat +
              2 * (cuccaroCarry b a carry).toNat = b.toNat + a.toNat + carry.toNat := by
            cases b <;> cases a <;> cases carry <;> decide
          simp only [cuccaroAddBits, carryAddOverflow, boolWordToNat_cons,
            List.length_cons, Nat.pow_succ]
          rw [Nat.mul_right_comm (2 ^ bs.length) 2]
          omega


private theorem values_congr (ws : List Wire) (s t : BasisState)
    (h : ∀ w ∈ ws, s w = t w) : wireValues ws s = wireValues ws t := by
  exact List.map_congr_left h

/-- Complete word action: addend and incoming carry are restored, the controlled sum is
written in place, and the gated overflow is XORed into an arbitrary initial output flag. -/
theorem controlledAddCarry_correct (bs as : List Wire) (q c f : Wire) (s : BasisState)
    (hlen : bs.length = as.length) (hnd : (q :: c :: f :: bs ++ as).Nodup) :
    let t := run (controlledAddCarry bs as q c f) s
    wireValues bs t = wireValues bs s ∧
      wireValues as t = (if s q then cuccaroAddBits (s c)
        (wireValues bs s) (wireValues as s) else wireValues as s) ∧
      t f = Bool.xor (s f) (s q && carryAddOverflow (s c)
        (wireValues bs s) (wireValues as s)) ∧
      ∀ w, w ∉ f :: as → t w = s w := by
  induction bs generalizing as s with
  | nil =>
      have : as = [] := List.length_eq_zero_iff.mp hlen.symm
      subst as
      simp [controlledAddCarry, run_cons, run_nil, applyGate, wireValues,
        carryAddOverflow, cuccaroAddBits, upd]
      intro w hne heq
      exact (hne heq).elim
  | cons b bs ih =>
      cases as with
      | nil => simp at hlen
      | cons a as =>
          have htail : bs.length = as.length := by simpa using hlen
          rcases List.nodup_cons.mp hnd with ⟨hq, hn⟩
          rcases List.nodup_cons.mp hn with ⟨hc, hn⟩
          rcases List.nodup_cons.mp hn with ⟨hf, hn⟩
          rcases List.nodup_append.mp hn with ⟨hbs, has, hcross⟩
          have hqc : q ≠ c := by intro h; exact hq (by simp [h])
          have hqf : q ≠ f := by intro h; exact hq (by simp [h])
          have hqb : q ≠ b := by intro h; exact hq (by simp [h])
          have hqa : q ≠ a := by intro h; exact hq (by simp [h])
          have hcf : c ≠ f := by intro h; exact hc (by simp [h])
          have hbc : b ≠ c := by intro h; exact hc (by simp [← h])
          have hac : a ≠ c := by intro h; exact hc (by simp [← h])
          have hbf : b ≠ f := by intro h; exact hf (by simp [← h])
          have haf : a ≠ f := by intro h; exact hf (by simp [← h])
          have hba : b ≠ a := by intro h; exact hcross b (by simp) a (by simp) h
          have hbbs := (List.nodup_cons.mp hbs).1
          have haas := (List.nodup_cons.mp has).1
          have hbas : b ∉ as := by
            intro h; exact hcross b (by simp) b (by simp [h]) rfl
          have habs : a ∉ bs := by
            intro h; exact hcross a (by simp [h]) a (by simp) rfl
          have hcbs : c ∉ bs := by intro h; exact hc (by simp [h])
          have hcas : c ∉ as := by intro h; exact hc (by simp [h])
          have hqbs : q ∉ bs := by intro h; exact hq (by simp [h])
          have hqas : q ∉ as := by intro h; exact hq (by simp [h])
          have hfbs : f ∉ bs := by intro h; exact hf (by simp [h])
          have hfas : f ∉ as := by intro h; exact hf (by simp [h])
          have hchild : (q :: c :: f :: bs ++ as).Nodup := by
            simp only [List.cons_append, List.nodup_cons, List.mem_cons, List.mem_append, not_or]
            refine ⟨⟨hqc, hqf, hqbs, hqas⟩, ⟨hcf, hcbs, hcas⟩,
              ⟨hfbs, hfas⟩, ?_⟩
            exact List.nodup_append.mpr ⟨(List.nodup_cons.mp hbs).2,
              (List.nodup_cons.mp has).2, fun x hx y hy =>
                hcross x (by simp [hx]) y (by simp [hy])⟩
          let first := run (carryAddMaj b a c) s
          have hfirst := run_carryAddMaj b a c s hba hbc hac
          have first_other (w : Wire) (hwb : w ≠ b) (hwa : w ≠ a) (hwc : w ≠ c) :
              first w = s w := by
            dsimp [first]; rw [hfirst]; simp [upd, hwb, hwa, hwc]
          have first_bs : wireValues bs first = wireValues bs s := by
            apply values_congr
            intro w hw
            exact first_other w (fun h => hbbs (h ▸ hw))
              (fun h => habs (h ▸ hw)) (fun h => hcbs (h ▸ hw))
          have first_as : wireValues as first = wireValues as s := by
            apply values_congr
            intro w hw
            exact first_other w (fun h => hbas (h ▸ hw))
              (fun h => haas (h ▸ hw)) (fun h => hcas (h ▸ hw))
          have first_q : first q = s q := first_other q hqb hqa hqc
          have first_f : first f = s f := first_other f hbf.symm haf.symm hcf.symm
          have first_c : first c = cuccaroCarry (s b) (s a) (s c) := by
            dsimp [first]; rw [hfirst]; simp [upd]
          let mid := run (controlledAddCarry bs as q c f) first
          have hm := ih as first htail hchild
          change wireValues bs mid = _ ∧ wireValues as mid = _ ∧ mid f = _ ∧ _ at hm
          have mid_out : ∀ w, w ∉ f :: as → mid w = first w := hm.2.2.2
          have mid_c : mid c = cuccaroCarry (s b) (s a) (s c) := by
            rw [mid_out c (by simp [hcf, hcas]), first_c]
          have mid_q : mid q = s q := by
            rw [mid_out q (by simp [hqf, hqas]), first_q]
          have mid_b : mid b = Bool.xor (s b) (s c) := by
            rw [mid_out b (by simp [hbf, hbas])]
            dsimp [first]; rw [hfirst]; simp [upd, hba, hbc]
          have mid_a : mid a = Bool.xor (s a) (s c) := by
            rw [mid_out a (by simp [haf, haas])]
            dsimp [first]; rw [hfirst]; simp [upd, hac]
          have hu := run_carryAddUma_prepared q b a c mid (s q) (s b) (s a) (s c)
            hqb hqa hqc hba hbc hac mid_q mid_b mid_a mid_c
          let last := run (carryAddUma q b a c) mid
          have last_other (w : Wire) (hwb : w ≠ b) (hwa : w ≠ a) (hwc : w ≠ c) :
              last w = mid w := by
            dsimp [last]; rw [hu]; simp [upd, hwb, hwa, hwc]
          have last_bs : wireValues bs last = wireValues bs mid := by
            apply values_congr
            intro w hw
            exact last_other w (fun h => hbbs (h ▸ hw))
              (fun h => habs (h ▸ hw)) (fun h => hcbs (h ▸ hw))
          have last_as : wireValues as last = wireValues as mid := by
            apply values_congr
            intro w hw
            exact last_other w (fun h => hbas (h ▸ hw))
              (fun h => haas (h ▸ hw)) (fun h => hcas (h ▸ hw))
          have last_b : last b = s b := by dsimp [last]; rw [hu]; simp [upd]
          have last_a : last a = if s q then cuccaroSum (s b) (s a) (s c) else s a := by
            dsimp [last]; rw [hu]; simp [upd, hba.symm]
          rw [controlledAddCarry, run_append, run_append]
          change wireValues (b :: bs) last = _ ∧ wireValues (a :: as) last = _ ∧
            last f = _ ∧ ∀ w, w ∉ f :: a :: as → last w = s w
          refine ⟨?_, ?_, ?_, ?_⟩
          · simp only [wireValues, List.map_cons]
            rw [last_b]
            congr 1
            exact last_bs.trans (hm.1.trans first_bs)
          · change last a :: wireValues as last = _
            rw [last_a, last_as, hm.2.1, first_q, first_c, first_bs, first_as]
            cases hcontrol : s q <;> simp [wireValues, cuccaroAddBits, hcontrol]
          · rw [last_other f hbf.symm haf.symm hcf.symm, hm.2.2.1,
              first_f, first_q, first_c, first_bs, first_as]
            rfl
          · intro w hw
            have hp : w ≠ f ∧ w ≠ a ∧ w ∉ as := by simpa using hw
            obtain ⟨hwf, hwa, hwas⟩ := hp
            by_cases hwb : w = b
            · subst w; exact last_b
            by_cases hwc : w = c
            · subst w; dsimp [last]; rw [hu]; simp [upd, hbc.symm, hac.symm]
            rw [last_other w hwb hwa hwc, mid_out w (by simp [hwf, hwas]),
              first_other w hwb hwa hwc]


/-- Direct modular arithmetic statement for the same concrete circuit. -/
theorem controlledAddCarry_value (bs as : List Wire) (q c f : Wire) (s : BasisState)
    (hlen : bs.length = as.length) (hnd : (q :: c :: f :: bs ++ as).Nodup) :
    boolWordToNat (wireValues as (run (controlledAddCarry bs as q c f) s)) =
      if s q then ((s c).toNat + boolWordToNat (wireValues bs s) +
        boolWordToNat (wireValues as s)) % (2 ^ bs.length)
      else boolWordToNat (wireValues as s) := by
  rw [(controlledAddCarry_correct bs as q c f s hlen hnd).2.1]
  cases hq : s q with
  | false => simp [hq]
  | true =>
      simp only [hq, Bool.true_eq, ↓reduceIte]
      simpa [wireValues] using boolWordToNat_cuccaroAddBits (s c)
        (wireValues bs s) (wireValues as s) (by simpa [wireValues] using hlen)

@[simp] theorem controlledAddCarry_HPFree (bs as : List Wire) (q c f : Wire) :
    HPFree (controlledAddCarry bs as q c f) := by
  induction bs generalizing as with
  | nil => cases as <;> simp [controlledAddCarry]
  | cons b bs ih => cases as <;> simp [controlledAddCarry, carryAddMaj, carryAddUma, ih]

/-- All primitive gate roles belong to the input/output registers and three scalar roles. -/
theorem controlledAddCarry_usesOnly (bs as : List Wire) (q c f : Wire) :
    PaperCircuitUsesOnly (q :: c :: f :: bs ++ as) (controlledAddCarry bs as q c f) := by
  induction bs generalizing as with
  | nil =>
      cases as <;> simp [controlledAddCarry, PaperCircuitUsesOnly,
        PaperGateUsesOnly, gateWires]
  | cons b bs ih =>
      cases as with
      | nil => simp [controlledAddCarry, PaperCircuitUsesOnly]
      | cons a as =>
          apply PaperCircuitUsesOnly.append
          · apply PaperCircuitUsesOnly.append
            · simp [carryAddMaj, PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires]
            · exact (ih as).mono (by
                intro w hw
                simp only [List.cons_append, List.mem_append, List.mem_cons] at hw ⊢
                rcases hw with h | h | h | h | h <;> simp_all)
          · simp [carryAddUma, PaperCircuitUsesOnly, PaperGateUsesOnly, gateWires]

theorem controlledAddCarry_wellFormed (bs as : List Wire) (q c f : Wire)
    (hlen : bs.length = as.length) (hnd : (q :: c :: f :: bs ++ as).Nodup) :
    CircuitWellFormed (controlledAddCarry bs as q c f) := by
  induction bs generalizing as with
  | nil =>
      cases as with
      | nil => simpa [controlledAddCarry, CircuitWellFormed, Gate.WellFormed, and_assoc] using hnd
      | cons => simp at hlen
  | cons b bs ih =>
      cases as with
      | nil => simp at hlen
      | cons a as =>
          have htail : bs.length = as.length := by simpa using hlen
          have hchild : (q :: c :: f :: bs ++ as).Nodup := by
            apply List.Nodup.sublist (l₂ := q :: c :: f :: (b :: bs) ++ a :: as) ?_ hnd
            simpa only [List.cons_append] using
              (List.Sublist.cons₂ q (List.Sublist.cons₂ c (List.Sublist.cons₂ f
                ((List.sublist_cons_self b bs).append (List.sublist_cons_self a as)))))
          have hr := ih as htail hchild
          simp only [List.cons_append, List.nodup_cons, List.nodup_append,
            List.mem_cons, List.mem_append, not_or] at hnd
          rw [controlledAddCarry, circuitWellFormed_append, circuitWellFormed_append]
          refine ⟨⟨?_, hr⟩, ?_⟩ <;>
            simp_all [carryAddMaj, carryAddUma, CircuitWellFormed, Gate.WellFormed, ne_comm]

/-- Exact coherent Toffoli count: one per forward cell, two per reverse cell,
and one controlled carry-output gate. -/
theorem controlledAddCarry_toffoliCount (bs as : List Wire) (q c f : Wire)
    (hlen : bs.length = as.length) :
    eeaToffoliCount (controlledAddCarry bs as q c f) = 3 * bs.length + 1 := by
  induction bs generalizing as with
  | nil => cases as <;> simp_all [controlledAddCarry, eeaToffoliCount]
  | cons b bs ih =>
      cases as with
      | nil => simp at hlen
      | cons a as =>
          have htail : bs.length = as.length := by simpa using hlen
          rw [controlledAddCarry, eeaToffoliCount_append, eeaToffoliCount_append, ih as htail]
          simp [carryAddMaj, carryAddUma, eeaToffoliCount]
          omega

theorem controlledAddCarry_cnotCount (bs as : List Wire) (q c f : Wire)
    (hlen : bs.length = as.length) :
    eeaCnotCount (controlledAddCarry bs as q c f) = 4 * bs.length := by
  induction bs generalizing as with
  | nil => cases as <;> simp_all [controlledAddCarry, eeaCnotCount]
  | cons b bs ih =>
      cases as with
      | nil => simp at hlen
      | cons a as =>
          have htail : bs.length = as.length := by simpa using hlen
          rw [controlledAddCarry, eeaCnotCount_append, eeaCnotCount_append, ih as htail]
          simp [carryAddMaj, carryAddUma, eeaCnotCount]
          omega

theorem controlledAddCarry_tCount (bs as : List Wire) (q c f : Wire)
    (hlen : bs.length = as.length) :
    tCount (controlledAddCarry bs as q c f) = 7 * (3 * bs.length + 1) := by
  induction bs generalizing as with
  | nil => cases as <;> simp_all [controlledAddCarry, tCount, tCost]
  | cons b bs ih =>
      cases as with
      | nil => simp at hlen
      | cons a as =>
          have htail : bs.length = as.length := by simpa using hlen
          rw [controlledAddCarry, tCount_append, tCount_append, ih as htail]
          simp [carryAddMaj, carryAddUma, tCount, tCost]
          omega


/-- Overflow is the integer quotient by the word modulus. -/
theorem carryAddOverflow_value (carry : Bool) (bs as : List Bool)
    (hlen : bs.length = as.length) :
    (carryAddOverflow carry bs as).toNat =
      (carry.toNat + boolWordToNat bs + boolWordToNat as) / 2 ^ bs.length := by
  rw [← carryAddBits_value carry bs as hlen,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos _)]
  have hlow : boolWordToNat (cuccaroAddBits carry bs as) < 2 ^ bs.length := by
    simpa [cuccaroAddBits_length carry bs as hlen] using
      boolWordToNat_lt_pow_two (cuccaroAddBits carry bs as)
  rw [Nat.div_eq_of_lt hlow, Nat.zero_add]

/-- The inverse restores the entire input state, including an arbitrary initial output flag. -/
theorem controlledSubCarry_after_add (bs as : List Wire) (q c f : Wire) (s : BasisState)
    (hlen : bs.length = as.length) (hnd : (q :: c :: f :: bs ++ as).Nodup) :
    run (controlledSubCarry bs as q c f) (run (controlledAddCarry bs as q c f) s) = s :=
  run_adjoint_run_classical _ (controlledAddCarry_wellFormed bs as q c f hlen hnd) s

/-- Concrete 256-bit carry-output adder: control 0, reusable carry 1, overflow 2,
addend wires 3–258, and accumulator wires 259–514. -/
def secp256k1ControlledAddCarry : Circuit :=
  controlledAddCarry (List.range' 3 256) (List.range' 259 256) 0 1 2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem secp256k1CarryAdd_layout :
    (0 :: 1 :: 2 :: List.range' 3 256 ++ List.range' 259 256).Nodup := by decide

private theorem carryAdd_mem_wires (bs as : List Wire) (q c f w : Wire)
    (hlen : bs.length = as.length) :
    w ∈ circuitWires (controlledAddCarry bs as q c f) ↔ w ∈ q :: c :: f :: bs ++ as := by
  induction bs generalizing as with
  | nil => cases as <;> simp_all [controlledAddCarry, circuitWires, gateWires]
  | cons b bs ih =>
      cases as with
      | nil => simp at hlen
      | cons a as =>
          have htail : bs.length = as.length := by simpa using hlen
          simp only [controlledAddCarry, circuitWires, List.flatMap_append, List.mem_append]
          change (w ∈ circuitWires (carryAddMaj b a c) ∨
            w ∈ circuitWires (controlledAddCarry bs as q c f)) ∨
            w ∈ circuitWires (carryAddUma q b a c) ↔ _
          rw [ih as htail]
          simp [carryAddMaj, carryAddUma, circuitWires, gateWires,
            or_assoc, or_left_comm, or_comm]

/-- Exact distinct-wire count, derived from the support of the actual gate stream. -/
theorem controlledAddCarry_qubitCount (bs as : List Wire) (q c f : Wire)
    (hlen : bs.length = as.length) (hnd : (q :: c :: f :: bs ++ as).Nodup) :
    qubitCount (controlledAddCarry bs as q c f) = 2 * bs.length + 3 := by
  have heq : (circuitWires (controlledAddCarry bs as q c f)).dedup.toFinset =
      (q :: c :: f :: bs ++ as).toFinset := by
    ext w
    simpa using carryAdd_mem_wires bs as q c f w hlen
  have hc := congrArg Finset.card heq
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _),
    List.toFinset_card_of_nodup hnd] at hc
  simpa [qubitCount, hlen, Nat.two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc

private theorem secp256k1CarryAdd_qubits : qubitCount secp256k1ControlledAddCarry = 515 := by
  simpa [secp256k1ControlledAddCarry] using controlledAddCarry_qubitCount
    (List.range' 3 256) (List.range' 259 256) 0 1 2 (by simp) secp256k1CarryAdd_layout

/-- Human-readable same-circuit certificate. With a clean incoming carry and overflow flag,
the accumulator receives the controlled 256-bit sum, the addend is preserved, the carry is
restored, and the overflow flag records the high bit. The exact circuit uses 769 Toffolis,
1,024 CNOTs, 5,383 coherent T gates, and 515 distinct wires. -/
theorem secp256k1ControlledAddCarry_correct_resources (s : BasisState)
    (hcarry : s 1 = false) (hflag : s 2 = false) :
    let after := run secp256k1ControlledAddCarry s
    let addend := boolWordToNat (wireValues (List.range' 3 256) s)
    let accumulator := boolWordToNat (wireValues (List.range' 259 256) s)
    boolWordToNat (wireValues (List.range' 259 256) after) =
        (accumulator + if s 0 then addend else 0) % 2 ^ 256 ∧
      wireValues (List.range' 3 256) after = wireValues (List.range' 3 256) s ∧
      after 1 = false ∧
      (after 2).toNat = (if s 0 then (accumulator + addend) / 2 ^ 256 else 0) ∧
      (∀ w, w ∉ 2 :: List.range' 259 256 → after w = s w) ∧
      CircuitWellFormed secp256k1ControlledAddCarry ∧
      HPFree secp256k1ControlledAddCarry ∧
      eeaToffoliCount secp256k1ControlledAddCarry = 769 ∧
      eeaCnotCount secp256k1ControlledAddCarry = 1024 ∧
      tCount secp256k1ControlledAddCarry = 5383 ∧
      qubitCount secp256k1ControlledAddCarry = 515 := by
  have hlen : (List.range' 3 256).length = (List.range' 259 256).length := by simp
  have hcorrect := controlledAddCarry_correct _ _ 0 1 2 s hlen secp256k1CarryAdd_layout
  have hvalue := controlledAddCarry_value _ _ 0 1 2 s hlen secp256k1CarryAdd_layout
  dsimp only
  refine ⟨?_, hcorrect.1, ?_, ?_, hcorrect.2.2.2, ?_, ?_, ?_, ?_, ?_,
    secp256k1CarryAdd_qubits⟩
  · change boolWordToNat (wireValues _ (run (controlledAddCarry _ _ 0 1 2) s)) = _
    rw [hvalue]
    have hbound : boolWordToNat (wireValues (List.range' 259 256) s) < 2 ^ 256 := by
      have h := boolWordToNat_lt_pow_two (wireValues (List.range' 259 256) s)
      simpa only [show (wireValues (List.range' 259 256) s).length = 256 by
        simp [wireValues]] using h
    cases hq : s 0 with
    | false =>
        simp only [hq, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        exact (Nat.mod_eq_of_lt hbound).symm
    | true => simp [hq, hcarry, Nat.add_comm]
  · change run (controlledAddCarry _ _ 0 1 2) s 1 = false
    rw [hcorrect.2.2.2 1 (by decide), hcarry]
  · change (run (controlledAddCarry _ _ 0 1 2) s 2).toNat = _
    rw [hcorrect.2.2.1, hflag, hcarry]
    have hover := carryAddOverflow_value false (wireValues (List.range' 3 256) s)
      (wireValues (List.range' 259 256) s) (by simp [wireValues])
    cases hq : s 0 with
    | false => simp [hq]
    | true => simpa [hq, wireValues, Nat.add_comm] using hover
  · exact controlledAddCarry_wellFormed _ _ 0 1 2 hlen secp256k1CarryAdd_layout
  · exact controlledAddCarry_HPFree _ _ 0 1 2
  · simpa [secp256k1ControlledAddCarry] using controlledAddCarry_toffoliCount _ _ 0 1 2 hlen
  · simpa [secp256k1ControlledAddCarry] using controlledAddCarry_cnotCount _ _ 0 1 2 hlen
  · simpa [secp256k1ControlledAddCarry] using controlledAddCarry_tCount _ _ 0 1 2 hlen


private theorem adjoint_mem_wires (circuit : Circuit) (w : Wire) :
    w ∈ circuitWires circuit.adjoint ↔ w ∈ circuitWires circuit := by
  induction circuit with
  | nil => simp [circuitWires]
  | cons gate circuit ih =>
      rw [circuit_adjoint_cons]
      simp only [circuitWires, List.flatMap_append, List.mem_append,
        List.flatMap_cons, List.flatMap_nil, List.append_nil] at *
      cases gate <;> simp_all [gateWires, Gate.adjoint, or_comm]

private theorem adjoint_qubitCount (circuit : Circuit) :
    qubitCount circuit.adjoint = qubitCount circuit := by
  have heq : (circuitWires circuit.adjoint).dedup.toFinset =
      (circuitWires circuit).dedup.toFinset := by
    ext w
    simpa using adjoint_mem_wires circuit w
  have hcard := congrArg Finset.card heq
  simpa [List.toFinset_card_of_nodup (List.nodup_dedup _)] using hcard

/-- Reversing the binary carry adder introduces no phase or Hadamard gates. -/
theorem controlledSubCarry_HPFree (bs as : List Wire) (q c f : Wire) :
    HPFree (controlledSubCarry bs as q c f) := by
  have h := controlledAddCarry_HPFree bs as q c f
  change HPFree (controlledAddCarry bs as q c f).adjoint
  generalize controlledAddCarry bs as q c f = circuit at *
  induction circuit with
  | nil => simp
  | cons g circuit ih =>
    have hp := (hpFree_cons g circuit).mp h
    rw [circuit_adjoint_cons,hpFree_append]
    refine ⟨ih hp.2,?_⟩
    cases g <;> simp_all [Gate.adjoint]

/-- Same-circuit inverse certificate: the literal reverse undoes the forward execution,
with the same exact gate and distinct-wire counts. -/
theorem controlledSubCarry_correct_resources (bs as : List Wire) (q c f : Wire)
    (s : BasisState) (hlen : bs.length = as.length)
    (hnd : (q :: c :: f :: bs ++ as).Nodup) :
    run (controlledSubCarry bs as q c f) (run (controlledAddCarry bs as q c f) s) = s ∧
      CircuitWellFormed (controlledSubCarry bs as q c f) ∧
      eeaToffoliCount (controlledSubCarry bs as q c f) = 3 * bs.length + 1 ∧
      eeaCnotCount (controlledSubCarry bs as q c f) = 4 * bs.length ∧
      tCount (controlledSubCarry bs as q c f) = 7 * (3 * bs.length + 1) ∧
      qubitCount (controlledSubCarry bs as q c f) = 2 * bs.length + 3 := by
  refine ⟨controlledSubCarry_after_add bs as q c f s hlen hnd, ?_, ?_, ?_, ?_, ?_⟩
  · exact (circuitWellFormed_adjoint _).2
      (controlledAddCarry_wellFormed bs as q c f hlen hnd)
  · rw [controlledSubCarry, eeaToffoliCount_adjoint]
    exact controlledAddCarry_toffoliCount bs as q c f hlen
  · rw [controlledSubCarry, eeaCnotCount_adjoint]
    exact controlledAddCarry_cnotCount bs as q c f hlen
  · rw [controlledSubCarry, tCount_adjoint]
    exact controlledAddCarry_tCount bs as q c f hlen
  · rw [controlledSubCarry, adjoint_qubitCount]
    exact controlledAddCarry_qubitCount bs as q c f hlen hnd

end ShorECDLP.Paper2607_13816
