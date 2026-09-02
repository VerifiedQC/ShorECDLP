import ShorECDLP.Submission.Arithmetic.Primitives
import Lean.Elab.Tactic.Omega

/-!
# One-ancilla in-place ripple addition

This file implements the basic Cuccaro majority/unmajority construction.  For equal-width,
pairwise-disjoint registers `source` and `target`, one carry wire, and one carry-output wire,

```text
inPlaceAddCarry(source, target, carry; carryOut)
```

preserves `source` and `carry`, replaces `target` by the low bits of
`source + target + carry`, and XORs the high bit into `carryOut`.  Unlike the older
out-of-place ripple adder, the source register itself temporarily stores the carry history, so
the circuit needs no width-sized carry bank.

The recursive program is the direct textbook circuit:

```text
MAJ(source[0], target[0], carry)
  ... recurse with source[0] as the next carry ...
UMA(source[0], target[0], carry)
```

At the empty tail, the final carry is copied to `carryOut`.
-/

namespace ShorECDLP

open Classical
open scoped ArithmeticNotation

/-- In-place majority.  It writes `majority(a,b,c)` into `a`, while `b` and `c` retain the
XORs needed by the later unmajority step. -/
def cuccaroMajority (a b c : Wire) : Circuit :=
  circuit! {
    gate! Gate.CX a b;
    gate! Gate.CX a c;
    gate! Gate.CCX c b a
  }

/-- Undo a Cuccaro majority and emit the corresponding sum bit into `b`. -/
def cuccaroUnmajorityAdd (a b c : Wire) : Circuit :=
  circuit! {
    gate! Gate.CCX c b a;
    gate! Gate.CX a c;
    gate! Gate.CX c b
  }

/-- One-ancilla in-place ripple addition with an XOR carry output.  Registers are LSB-first. -/
def inPlaceAddCarry : List Wire → List Wire → Wire → Wire → Circuit
  | [], [], carry, carryOut => circuit! { gate! Gate.CX carry carryOut }
  | a :: as, b :: bs, carry, carryOut =>
      circuit! {
        cuccaroMajority a b carry;
        inPlaceAddCarry as bs a carryOut;
        cuccaroUnmajorityAdd a b carry
      }
  | _, _, _, _ => circuit! {}

private def majorityBool (a b c : Bool) : Bool :=
  Bool.xor (Bool.xor (a && b) (a && c)) (b && c)

private def sumBool (a b c : Bool) : Bool :=
  Bool.xor (Bool.xor a b) c

/-- Exact values written by one majority cell. -/
private theorem run_cuccaroMajority (a b c : Wire) (st : BasisState)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    let after := run (cuccaroMajority a b c) st
    after a = majorityBool (st a) (st b) (st c) ∧
      after b = Bool.xor (st b) (st a) ∧
      after c = Bool.xor (st c) (st a) ∧
      ∀ w, w ≠ a → w ≠ b → w ≠ c → after w = st w := by
  dsimp only
  constructor
  · simp only [cuccaroMajority, run_cons, run_nil, applyGate, upd_same]
    simp [upd, hab, hac, hbc, hbc.symm, majorityBool]
    cases st a <;> cases st b <;> cases st c <;> decide
  constructor
  · simp only [cuccaroMajority, run_cons, run_nil, applyGate]
    simp [upd, hbc, hab.symm]
  constructor
  · simp only [cuccaroMajority, run_cons, run_nil, applyGate]
    simp [upd, hab, hac.symm, hbc.symm]
  · intro w hwa hwb hwc
    simp only [cuccaroMajority, run_cons, run_nil, applyGate]
    simp [upd, hwa, hwb, hwc]

/-- `UMA` restores the original source/carry bits and emits the low sum bit after a matching
majority, even if an intervening circuit has changed unrelated wires. -/
private theorem run_cuccaroUnmajorityAdd_of_majority
    (a b c : Wire) (before mid : BasisState)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : mid a = majorityBool (before a) (before b) (before c))
    (hb : mid b = Bool.xor (before b) (before a))
    (hc : mid c = Bool.xor (before c) (before a)) :
    let after := run (cuccaroUnmajorityAdd a b c) mid
    after a = before a ∧ after b = sumBool (before a) (before b) (before c) ∧
      after c = before c := by
  dsimp only
  simp only [cuccaroUnmajorityAdd, run_cons, run_nil, applyGate, upd_same]
  simp [upd, hab, hac, hbc, hab.symm, hac.symm, hbc.symm, ha, hb, hc,
    majorityBool, sumBool]
  cases before a <;> cases before b <;> cases before c <;> decide

/-- A majority cell touches only its three wires. -/
private theorem cuccaroMajority_other (a b c w : Wire) (st : BasisState)
    (hwa : w ≠ a) (hwb : w ≠ b) (hwc : w ≠ c) :
    run (cuccaroMajority a b c) st w = st w := by
  simp only [cuccaroMajority, run_cons, run_nil, applyGate]
  simp [upd, hwa, hwb, hwc]

/-- An unmajority cell touches only its three wires. -/
private theorem cuccaroUnmajorityAdd_other (a b c w : Wire) (st : BasisState)
    (hwa : w ≠ a) (hwb : w ≠ b) (hwc : w ≠ c) :
    run (cuccaroUnmajorityAdd a b c) st w = st w := by
  simp only [cuccaroUnmajorityAdd, run_cons, run_nil, applyGate]
  simp [upd, hwa, hwb, hwc]

theorem inPlaceAddCarry_nodup_parts (source target : List Wire) (carry carryOut : Wire)
    (hnd : (source ++ (target ++ [carry, carryOut])).Nodup) :
    source.Nodup ∧ target.Nodup ∧ carry ≠ carryOut ∧
      (∀ w ∈ source, w ∉ target ∧ w ≠ carry ∧ w ≠ carryOut) ∧
      (∀ w ∈ target, w ≠ carry ∧ w ≠ carryOut) := by
  rw [List.nodup_append] at hnd
  obtain ⟨hsource, hrest, hsourceRest⟩ := hnd
  rw [List.nodup_append] at hrest
  obtain ⟨htarget, hflags, htargetFlags⟩ := hrest
  have hcarryOut : carry ≠ carryOut := by simpa using hflags
  refine ⟨hsource, htarget, hcarryOut, ?_, ?_⟩
  · intro w hw
    refine ⟨?_, ?_, ?_⟩
    · intro hwt
      exact hsourceRest w hw w (by simp [hwt]) rfl
    · intro e
      exact hsourceRest w hw carry (by simp) e
    · intro e
      exact hsourceRest w hw carryOut (by simp) e
  · intro w hw
    constructor
    · intro e
      exact htargetFlags w hw carry (by simp) e
    · intro e
      exact htargetFlags w hw carryOut (by simp) e

/-- The recursive carry rotation keeps a duplicate-free wire layout. -/
private theorem recursive_nodup (a b carry carryOut : Wire) (as bs : List Wire)
    (hnd : ((a :: as) ++ ((b :: bs) ++ [carry, carryOut])).Nodup) :
    (as ++ (bs ++ [a, carryOut])).Nodup := by
  have hskipB : List.Sublist bs (b :: bs) := (List.Sublist.refl bs).cons b
  have hskipCarry : List.Sublist (carryOut :: []) (carry :: carryOut :: []) :=
    (List.Sublist.refl (carryOut :: [])).cons carry
  have htail : List.Sublist (bs ++ (carryOut :: []))
      ((b :: bs) ++ (carry :: carryOut :: [])) :=
    List.Sublist.append hskipB hskipCarry
  have hprefix : List.Sublist ((a :: as) ++ (bs ++ [carryOut]))
      ((a :: as) ++ ((b :: bs) ++ [carry, carryOut])) :=
    htail.append_left (a :: as)
  have hsmall : ((a :: as) ++ (bs ++ [carryOut])).Nodup :=
    hprefix.nodup hnd
  have hperm : List.Perm (as ++ (bs ++ [a, carryOut]))
      ((a :: as) ++ (bs ++ [carryOut])) := by
    simpa [List.append_assoc] using
      (List.perm_middle (l₁ := as ++ bs) (l₂ := carryOut :: []) (a := a))
  exact hsmall.perm hperm.symm

/-- The one-ancilla adder's exact classical action.  The carry-output bit must start clean;
the source register and incoming carry are restored, while target plus the high output bit is
the ordinary sum.  Net action is confined to `target` and `carryOut`. -/
theorem inPlaceAddCarry_correct :
    ∀ (source target : List Wire) (carry carryOut : Wire) (st : BasisState),
      target.length = source.length →
      (source ++ (target ++ [carry, carryOut])).Nodup →
      st carryOut = false →
      let after := run (inPlaceAddCarry source target carry carryOut) st
      AgreesOn source st after ∧
        after carry = st carry ∧
        after⟦ᵣtarget⟧ + 2 ^ source.length * bit after carryOut =
          st⟦ᵣsource⟧ + st⟦ᵣtarget⟧ + bit st carry ∧
        ∀ w, w ∉ target → w ≠ carryOut → after w = st w := by
  intro source
  induction source with
  | nil =>
      intro target carry carryOut st hlen hnd hcarryOut
      have htarget : target = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst target
      have hne : carry ≠ carryOut :=
        (inPlaceAddCarry_nodup_parts ([] : List Wire) ([] : List Wire) carry carryOut hnd).2.2.1
      dsimp only
      constructor
      · intro w hw
        simp at hw
      constructor
      · simp [inPlaceAddCarry, run_cons, run_nil, applyGate, upd, hne]
      constructor
      · simp only [inPlaceAddCarry, regValue, List.length_nil, Nat.pow_zero,
          run_cons, run_nil, applyGate, upd_same, bit]
        rw [hcarryOut]
        cases st carry <;> simp
      · intro w _ hw
        simp [inPlaceAddCarry, run_cons, run_nil, applyGate, upd, hw]
  | cons a as ih =>
      intro target carry carryOut st hlen hnd hcarryOut
      cases target with
      | nil => simp at hlen
      | cons b bs =>
          have hlenTail : bs.length = as.length := by simpa using hlen
          obtain ⟨hsourceNd, htargetNd, hcarryNeOut, hsourceParts, htargetParts⟩ :=
            inPlaceAddCarry_nodup_parts (a :: as) (b :: bs) carry carryOut hnd
          have haParts := hsourceParts a (List.mem_cons_self ..)
          have hbParts := htargetParts b (List.mem_cons_self ..)
          have hab : a ≠ b := by
            intro e
            exact haParts.1 (by simp [e])
          have hac : a ≠ carry := haParts.2.1
          have haOut : a ≠ carryOut := haParts.2.2
          have hbc : b ≠ carry := hbParts.1
          have hbOut : b ≠ carryOut := hbParts.2
          have haAs : a ∉ as := (List.nodup_cons.mp hsourceNd).1
          have hbBs : b ∉ bs := (List.nodup_cons.mp htargetNd).1
          have hrecursive : (as ++ (bs ++ [a, carryOut])).Nodup :=
            recursive_nodup a b carry carryOut as bs hnd
          let st₁ := run (cuccaroMajority a b carry) st
          let st₂ := run (inPlaceAddCarry as bs a carryOut) st₁
          let after := run (cuccaroUnmajorityAdd a b carry) st₂
          have hmaj := run_cuccaroMajority a b carry st hab hac hbc
          have hmajA : st₁ a = majorityBool (st a) (st b) (st carry) := hmaj.1
          have hcarryOut₁ : st₁ carryOut = false := by
            rw [show st₁ carryOut = st carryOut from
              cuccaroMajority_other a b carry carryOut st
                haOut.symm hbOut.symm hcarryNeOut.symm]
            exact hcarryOut
          have hih := ih bs a carryOut st₁ hlenTail hrecursive hcarryOut₁
          dsimp only at hih
          obtain ⟨hsourceTail, hcarryTail, hsumTail, houtsideTail⟩ := hih
          have hbTail : st₂ b = st₁ b := by
            exact houtsideTail b hbBs hbOut
          have hcTail : st₂ carry = st₁ carry := by
            apply houtsideTail carry
            · intro hw
              exact (htargetParts carry (List.mem_cons_of_mem b hw)).1 rfl
            · exact hcarryNeOut
          have huma := run_cuccaroUnmajorityAdd_of_majority a b carry st st₂
            hab hac hbc
            (hcarryTail.trans hmaj.1)
            (hbTail.trans hmaj.2.1)
            (hcTail.trans hmaj.2.2.1)
          change after a = st a ∧
            after b = sumBool (st a) (st b) (st carry) ∧
            after carry = st carry at huma
          have hrun :
              run (inPlaceAddCarry (a :: as) (b :: bs) carry carryOut) st = after := by
            simp [inPlaceAddCarry, after, st₂, st₁, run_append]
          have hsourceMaj : st₁⟦ᵣas⟧ = st⟦ᵣas⟧ := by
            apply regValue_congr
            intro w hw
            have hwParts := hsourceParts w (List.mem_cons_of_mem a hw)
            exact cuccaroMajority_other a b carry w st
              (fun e => haAs (e ▸ hw))
              (fun e => hwParts.1 (by simp [e]))
              hwParts.2.1
          have htargetMaj : st₁⟦ᵣbs⟧ = st⟦ᵣbs⟧ := by
            apply regValue_congr
            intro w hw
            have hwParts := htargetParts w (List.mem_cons_of_mem b hw)
            exact cuccaroMajority_other a b carry w st
              (fun e => haParts.1 (List.mem_cons_of_mem b (e ▸ hw)))
              (fun e => hbBs (e ▸ hw))
              hwParts.1
          have htargetTail : after⟦ᵣbs⟧ = st₂⟦ᵣbs⟧ := by
            apply regValue_congr
            intro w hw
            have hwParts := htargetParts w (List.mem_cons_of_mem b hw)
            exact cuccaroUnmajorityAdd_other a b carry w st₂
              (fun e => haParts.1 (List.mem_cons_of_mem b (e ▸ hw)))
              (fun e => hbBs (e ▸ hw))
              hwParts.1
          have hcarryOutFinal : after carryOut = st₂ carryOut :=
            cuccaroUnmajorityAdd_other a b carry carryOut st₂
              haOut.symm hbOut.symm hcarryNeOut.symm
          have hsumTail' :
              st₂⟦ᵣbs⟧ + 2 ^ as.length * bit st₂ carryOut =
                st⟦ᵣas⟧ + st⟦ᵣbs⟧ +
                  (if majorityBool (st a) (st b) (st carry) then 1 else 0) := by
            change st₂⟦ᵣbs⟧ + 2 ^ as.length * bit st₂ carryOut =
              st₁⟦ᵣas⟧ + st₁⟦ᵣbs⟧ + bit st₁ a at hsumTail
            simpa [hsourceMaj, htargetMaj, bit, hmajA] using hsumTail
          clear hsumTail
          have hcolumn :
              (if st a then 1 else 0) + (if st b then 1 else 0) +
                  (if st carry then 1 else 0) =
                (if after b then 1 else 0) +
                  2 * (if majorityBool (st a) (st b) (st carry) then 1 else 0) := by
            simpa [huma.2.1, sumBool, majorityBool] using
              bit_column (st a) (st b) (st carry)
          have hsourceFinal : AgreesOn (a :: as) st after := by
            intro w hw
            rcases List.mem_cons.mp hw with rfl | hw
            · exact huma.1
            · have hwParts := hsourceParts w (List.mem_cons_of_mem a hw)
              calc
                after w = st₂ w := cuccaroUnmajorityAdd_other a b carry w st₂
                  (fun e => haAs (e ▸ hw))
                  (fun e => hwParts.1 (by simp [e]))
                  hwParts.2.1
                _ = st₁ w := hsourceTail w hw
                _ = st w := cuccaroMajority_other a b carry w st
                  (fun e => haAs (e ▸ hw))
                  (fun e => hwParts.1 (by simp [e]))
                  hwParts.2.1
          have hnumeric :
              after⟦ᵣb :: bs⟧ + 2 ^ (a :: as).length * bit after carryOut =
                st⟦ᵣa :: as⟧ + st⟦ᵣb :: bs⟧ + bit st carry := by
            rw [regValue_cons, regValue_cons, regValue_cons, htargetTail,
              List.length_cons, Nat.pow_succ]
            rw [show bit after carryOut = bit st₂ carryOut by
              simp [bit, hcarryOutFinal]]
            have hmul :
                (2 ^ as.length * 2) * bit st₂ carryOut =
                  2 * (2 ^ as.length * bit st₂ carryOut) := by
              simp [Nat.mul_assoc, Nat.mul_comm]
            rw [hmul]
            simp only [bit] at hsumTail' ⊢
            omega
          have houtside : ∀ w, w ∉ b :: bs → w ≠ carryOut → after w = st w := by
            intro w hwTarget hwOut
            have hwb : w ≠ b := by
              intro e
              exact hwTarget (e ▸ List.mem_cons_self)
            have hwbs : w ∉ bs := by
              intro hw
              exact hwTarget (List.mem_cons_of_mem b hw)
            by_cases hwa : w = a
            · subst w
              exact huma.1
            by_cases hwc : w = carry
            · subst w
              exact huma.2.2
            calc
              after w = st₂ w := cuccaroUnmajorityAdd_other a b carry w st₂
                hwa hwb hwc
              _ = st₁ w := houtsideTail w hwbs hwOut
              _ = st w := cuccaroMajority_other a b carry w st hwa hwb hwc

          rw [hrun]
          exact ⟨hsourceFinal, huma.2.2, hnumeric, houtside⟩

/-! ## Structural and cost certificates -/

/-- One majority cell costs one Toffoli. -/
@[simp] theorem cuccaroMajority_tCount (a b c : Wire) :
    tCount (cuccaroMajority a b c) = 7 := rfl

/-- One unmajority-add cell costs one Toffoli. -/
@[simp] theorem cuccaroUnmajorityAdd_tCount (a b c : Wire) :
    tCount (cuccaroUnmajorityAdd a b c) = 7 := rfl

/-- The in-place adder uses two Toffolis per bit. -/
theorem inPlaceAddCarry_tCount :
    ∀ (source target : List Wire) (carry carryOut : Wire),
      target.length = source.length →
      tCount (inPlaceAddCarry source target carry carryOut) = 14 * source.length := by
  intro source
  induction source with
  | nil =>
      intro target carry carryOut hlen
      have htarget : target = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst target
      rfl
  | cons a as ih =>
      intro target carry carryOut hlen
      cases target with
      | nil => simp at hlen
      | cons b bs =>
          have hlenTail : bs.length = as.length := by simpa using hlen
          rw [inPlaceAddCarry, tCount_append, tCount_append,
            cuccaroMajority_tCount, cuccaroUnmajorityAdd_tCount,
            ih bs a carryOut hlenTail]
          simp only [List.length_cons, Nat.mul_succ]
          omega

/-- The in-place adder is arithmetic: it contains no Hadamard or phase gates. -/
theorem inPlaceAddCarry_HPFree (source target : List Wire) (carry carryOut : Wire) :
    HPFree (inPlaceAddCarry source target carry carryOut) := by
  induction source generalizing target carry with
  | nil => cases target <;> simp [inPlaceAddCarry]
  | cons a as ih =>
      cases target with
      | nil => simp [inPlaceAddCarry]
      | cons b bs =>
          rw [inPlaceAddCarry, hpFree_append, hpFree_append]
          exact ⟨⟨by simp [cuccaroMajority], ih bs a⟩,
            by simp [cuccaroUnmajorityAdd]⟩

/-- One majority cell is physically well-formed on three distinct wires. -/
theorem cuccaroMajority_wellFormed (a b c : Wire)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    CircuitWellFormed (cuccaroMajority a b c) := by
  simp only [cuccaroMajority, circuitWellFormed_cons, circuitWellFormed_nil,
    Gate.WellFormed, and_true]
  exact ⟨hab, hac, hbc.symm, hac.symm, hab.symm⟩

/-- One unmajority-add cell is physically well-formed on three distinct wires. -/
theorem cuccaroUnmajorityAdd_wellFormed (a b c : Wire)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    CircuitWellFormed (cuccaroUnmajorityAdd a b c) := by
  simp only [cuccaroUnmajorityAdd, circuitWellFormed_cons, circuitWellFormed_nil,
    Gate.WellFormed, and_true]
  exact ⟨⟨hbc.symm, hac.symm, hab.symm⟩, hac, hbc.symm⟩

/-- The complete in-place adder is well-formed on a duplicate-free layout. -/
theorem inPlaceAddCarry_wellFormed :
    ∀ (source target : List Wire) (carry carryOut : Wire),
      target.length = source.length →
      (source ++ (target ++ [carry, carryOut])).Nodup →
      CircuitWellFormed (inPlaceAddCarry source target carry carryOut) := by
  intro source
  induction source with
  | nil =>
      intro target carry carryOut hlen hnd
      have htarget : target = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst target
      have hne : carry ≠ carryOut :=
        (inPlaceAddCarry_nodup_parts ([] : List Wire) ([] : List Wire) carry carryOut hnd).2.2.1
      simp [inPlaceAddCarry, Gate.WellFormed, hne]
  | cons a as ih =>
      intro target carry carryOut hlen hnd
      cases target with
      | nil => simp at hlen
      | cons b bs =>
          have hlenTail : bs.length = as.length := by simpa using hlen
          obtain ⟨_, _, _, hsourceParts, htargetParts⟩ :=
            inPlaceAddCarry_nodup_parts (a :: as) (b :: bs) carry carryOut hnd
          have haParts := hsourceParts a (List.mem_cons_self ..)
          have hbParts := htargetParts b (List.mem_cons_self ..)
          have hab : a ≠ b := by
            intro e
            exact haParts.1 (by simp [e])
          have hac : a ≠ carry := haParts.2.1
          have hbc : b ≠ carry := hbParts.1
          have hrecursive : (as ++ (bs ++ [a, carryOut])).Nodup :=
            recursive_nodup a b carry carryOut as bs hnd
          rw [inPlaceAddCarry, circuitWellFormed_append, circuitWellFormed_append]
          exact ⟨⟨cuccaroMajority_wellFormed a b carry hab hac hbc,
            ih bs a carryOut hlenTail hrecursive⟩,
            cuccaroUnmajorityAdd_wellFormed a b carry hab hac hbc⟩

/-- The exact named-wire support of the in-place adder. -/
def inPlaceAddCarryFootprint (source target : List Wire) (carry carryOut : Wire) :
    List Wire := source ++ target ++ [carry, carryOut]

/-- A majority cell uses only its three named wires. -/
theorem cuccaroMajority_usesOnly (a b c : Wire) :
    CircuitUsesOnly [a, b, c] (cuccaroMajority a b c) := by
  simp [CircuitUsesOnly, cuccaroMajority, Gate.UsesOnly]

/-- An unmajority-add cell uses only its three named wires. -/
theorem cuccaroUnmajorityAdd_usesOnly (a b c : Wire) :
    CircuitUsesOnly [a, b, c] (cuccaroUnmajorityAdd a b c) := by
  simp [CircuitUsesOnly, cuccaroUnmajorityAdd, Gate.UsesOnly]

/-- The recursive adder never touches or controls on an undeclared wire. -/
theorem inPlaceAddCarry_usesOnly :
    ∀ (source target : List Wire) (carry carryOut : Wire),
      CircuitUsesOnly (inPlaceAddCarryFootprint source target carry carryOut)
        (inPlaceAddCarry source target carry carryOut) := by
  intro source
  induction source with
  | nil =>
      intro target carry carryOut
      cases target
      · simp [inPlaceAddCarry, inPlaceAddCarryFootprint, CircuitUsesOnly, Gate.UsesOnly]
      · simp [inPlaceAddCarry, inPlaceAddCarryFootprint, CircuitUsesOnly]
  | cons a as ih =>
      intro target carry carryOut
      cases target with
      | nil => simp [inPlaceAddCarry, inPlaceAddCarryFootprint, CircuitUsesOnly]
      | cons b bs =>
          rw [inPlaceAddCarry]
          apply Arithmetic.usesOnly_append
          · apply Arithmetic.usesOnly_append
            · apply Arithmetic.usesOnly_mono (cuccaroMajority_usesOnly a b carry)
              intro w hw
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
              simp [inPlaceAddCarryFootprint]
              rcases hw with rfl | rfl | rfl <;> simp
            · apply Arithmetic.usesOnly_mono (ih bs a carryOut)
              intro w hw
              simp only [inPlaceAddCarryFootprint, List.mem_append,
                List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
              rcases hw with (hw | hw) | hw | hw
              · exact Or.inl (Or.inl (Or.inr hw))
              · exact Or.inl (Or.inr (Or.inr hw))
              · subst w
                simp
              · subst w
                simp
          · apply Arithmetic.usesOnly_mono (cuccaroUnmajorityAdd_usesOnly a b carry)
            intro w hw
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
            simp [inPlaceAddCarryFootprint]
            rcases hw with rfl | rfl | rfl <;> simp

end ShorECDLP
