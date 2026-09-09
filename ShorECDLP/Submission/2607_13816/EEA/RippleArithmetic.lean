import ShorECDLP.Submission.«2607_13816».EEA.WordNat
import ShorECDLP.Submission.«2607_13816».EEA.Ripple

/-! # Arithmetic interpretation of the two-pass controlled ripple -/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum

private def rippleWordFirst (mode : RippleMode) (control : Bool) :
    List Bool → List Bool → Bool → List Bool × List Bool × Bool
  | t :: ts, a :: ads, carry =>
    let rest := rippleWordFirst mode control ts ads carry
    let cell := rippleFirstBits mode control ⟨t, a, rest.2.2⟩
    (cell.target :: rest.1, cell.addend :: rest.2.1, cell.carry)
  | ts, ads, carry => (ts, ads, carry)

private def rippleWordSecond (mode : RippleMode) (control : Bool) :
    List Bool → List Bool → Bool → List Bool × List Bool × Bool
  | t :: ts, a :: ads, carry =>
    let cell := rippleSecondBits mode control ⟨t, a, carry⟩
    let rest := rippleWordSecond mode control ts ads cell.carry
    (cell.target :: rest.1, cell.addend :: rest.2.1, rest.2.2)
  | ts, ads, carry => (ts, ads, carry)

private def rippleExpected (mode : RippleMode) (control : Bool) :
    List Bool → List Bool → Bool → List Bool × Bool
  | t :: ts, a :: ads, carry =>
    let rest := rippleExpected mode control ts ads carry
    ((if control then t ^^ a ^^ rest.2 else t) :: rest.1,
      (rippleFirstBits mode control ⟨t, a, rest.2⟩).carry)
  | ts, _, carry => (ts, carry)

private theorem rippleCell_round (mode : RippleMode) (control t a carry : Bool) :
    rippleSecondBits mode control (rippleFirstBits mode control ⟨t,a,carry⟩) =
      ⟨if control then t ^^ a ^^ carry else t, a, carry⟩ := by
  cases mode <;> cases control <;> cases t <;> cases a <;> cases carry <;> decide

private theorem rippleWords_fusion (mode : RippleMode) (control : Bool)
    (ts ads : List Bool) (carry : Bool) (hlen : ts.length = ads.length) :
    let first := rippleWordFirst mode control ts ads carry
    let second := rippleWordSecond mode control first.1 first.2.1 first.2.2
    second = ((rippleExpected mode control ts ads carry).1, ads, carry) ∧
      first.2.2 = (rippleExpected mode control ts ads carry).2 := by
  induction ts generalizing ads carry with
  | nil =>
    have ha : ads = [] := List.eq_nil_of_length_eq_zero hlen.symm
    subst ads
    exact ⟨rfl,rfl⟩
  | cons t ts ih =>
    cases ads with
    | nil => simp at hlen
    | cons a ads =>
      have ht : ts.length = ads.length := by simpa using hlen
      have hr := ih ads carry ht
      dsimp only at hr ⊢
      simp only [rippleWordFirst, rippleWordSecond, rippleExpected]
      have hc := rippleCell_round mode control t a (rippleWordFirst mode control ts ads carry).2.2
      cases hf : rippleFirstBits mode control ⟨t,a,(rippleWordFirst mode control ts ads carry).2.2⟩
      rw [hf] at hc
      rw [hc]
      simp only
      rw [hr.1, hr.2]
      constructor
      · rfl
      · rw [← hr.2, hf]

private theorem rippleValue_append (xs ys : List Bool) :
    boolWordToNat (xs ++ ys) = boolWordToNat xs + 2^xs.length * boolWordToNat ys := by
  induction xs with
  | nil => simp
  | cons b xs ih =>
    simp only [List.cons_append, boolWordToNat_cons, List.length_cons, ih, Nat.pow_succ]
    ring

private theorem rippleValue_cons (b : Bool) (bits : List Bool) :
    boolWordToNat (b :: bits).reverse = boolWordToNat bits.reverse + 2^bits.length * b.toNat := by
  rw [List.reverse_cons, rippleValue_append]
  simp

private theorem rippleCell_add_value (t a c : Bool) :
    (t ^^ a ^^ c).toNat + 2*(rippleFirstBits .add true ⟨t,a,c⟩).carry.toNat =
      t.toNat+a.toNat+c.toNat := by
  cases t <;> cases a <;> cases c <;> decide

private theorem rippleCell_sub_value (t a c : Bool) :
    (t ^^ a ^^ c).toNat+a.toNat+c.toNat =
      t.toNat+2*(rippleFirstBits .sub true ⟨t,a,c⟩).carry.toNat := by
  cases t <;> cases a <;> cases c <;> decide

private theorem rippleExpected_length (mode : RippleMode) (control : Bool)
    (ts ads : List Bool) (carry : Bool) :
    (rippleExpected mode control ts ads carry).1.length = ts.length := by
  induction ts generalizing ads carry with
  | nil => rfl
  | cons t ts ih =>
    cases ads with
    | nil => rfl
    | cons a ads => simp only [rippleExpected, List.length_cons, ih]

private theorem rippleExpected_add_value (ts ads : List Bool) (carry : Bool)
    (hlen : ts.length = ads.length) :
    boolWordToNat (rippleExpected .add true ts ads carry).1.reverse +
      2^ts.length * (rippleExpected .add true ts ads carry).2.toNat =
      boolWordToNat ts.reverse + boolWordToNat ads.reverse + carry.toNat := by
  induction ts generalizing ads carry with
  | nil =>
    have ha : ads = [] := List.eq_nil_of_length_eq_zero hlen.symm
    subst ads
    simp [rippleExpected]
  | cons t ts ih =>
    cases ads with
    | nil => simp at hlen
    | cons a ads =>
      have ht : ts.length = ads.length := by simpa using hlen
      have hv := ih ads carry ht
      have hc := rippleCell_add_value t a (rippleExpected .add true ts ads carry).2
      simp only [rippleExpected, ↓reduceIte, rippleValue_cons, List.length_cons,
        rippleExpected_length, Nat.pow_succ, ← ht]
      have hs := congrArg (fun x : Nat => 2^ts.length * x) hc
      nlinarith [hs]

private theorem rippleExpected_sub_value (ts ads : List Bool) (carry : Bool)
    (hlen : ts.length = ads.length) :
    boolWordToNat (rippleExpected .sub true ts ads carry).1.reverse +
      boolWordToNat ads.reverse + carry.toNat = boolWordToNat ts.reverse +
        2^ts.length * (rippleExpected .sub true ts ads carry).2.toNat := by
  induction ts generalizing ads carry with
  | nil =>
    have ha : ads = [] := List.eq_nil_of_length_eq_zero hlen.symm
    subst ads
    simp [rippleExpected]
  | cons t ts ih =>
    cases ads with
    | nil => simp at hlen
    | cons a ads =>
      have ht : ts.length = ads.length := by simpa using hlen
      have hv := ih ads carry ht
      have hc := rippleCell_sub_value t a (rippleExpected .sub true ts ads carry).2
      simp only [rippleExpected, ↓reduceIte, rippleValue_cons, List.length_cons,
        rippleExpected_length, Nat.pow_succ, ← ht]
      have hs := congrArg (fun x : Nat => 2^ts.length * x) hc
      nlinarith [hs]

private theorem rippleExpected_add_mod (ts ads : List Bool) (carry : Bool)
    (hlen : ts.length = ads.length) :
    boolWordToNat (rippleExpected .add true ts ads carry).1.reverse =
      (boolWordToNat ts.reverse + boolWordToNat ads.reverse + carry.toNat) % 2^ts.length := by
  have h := rippleExpected_add_value ts ads carry hlen
  have hb := boolWordToNat_lt_pow_two (rippleExpected .add true ts ads carry).1.reverse
  simp only [List.length_reverse, rippleExpected_length] at hb
  rw [← h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]

private theorem rippleExpected_sub_mod (ts ads : List Bool) (carry : Bool)
    (hlen : ts.length = ads.length) :
    boolWordToNat (rippleExpected .sub true ts ads carry).1.reverse =
      (boolWordToNat ts.reverse + 2^ts.length - boolWordToNat ads.reverse - carry.toNat) %
        2^ts.length := by
  have h := rippleExpected_sub_value ts ads carry hlen
  have hb := boolWordToNat_lt_pow_two (rippleExpected .sub true ts ads carry).1.reverse
  simp only [List.length_reverse, rippleExpected_length] at hb
  cases hc : (rippleExpected .sub true ts ads carry).2 with
  | false =>
    rw [hc] at h
    simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at h
    rw [show boolWordToNat ts.reverse + 2^ts.length - boolWordToNat ads.reverse - carry.toNat =
        boolWordToNat (rippleExpected .sub true ts ads carry).1.reverse + 2^ts.length by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt hb]
  | true =>
    rw [hc] at h
    simp only [Bool.toNat_true, Nat.mul_one] at h
    rw [show boolWordToNat ts.reverse + 2^ts.length - boolWordToNat ads.reverse - carry.toNat =
        boolWordToNat (rippleExpected .sub true ts ads carry).1.reverse by omega,
      Nat.mod_eq_of_lt hb]

private theorem rippleExpected_disabled (mode : RippleMode) (ts ads : List Bool) (carry : Bool) :
    rippleExpected mode false ts ads carry = (ts, carry) := by
  induction ts generalizing ads carry with
  | nil => rfl
  | cons t ts ih =>
    cases ads with
    | nil => rfl
    | cons a ads =>
      simp only [rippleExpected, ih, Bool.false_eq_true, ↓reduceIte]
      cases mode <;> cases t <;> cases a <;> cases carry <;> rfl

private theorem rippleWrite_outside (t a c : Wire) (bits : RippleCellBits) (state : BasisState)
    (w : Wire) (ht : w ≠ t) (ha : w ≠ a) (hc : w ≠ c) :
    writeRippleCell t a c bits state w = state w := by
  simp [writeRippleCell, upd, ht, ha, hc]

private theorem rippleFirst_outside (mode : RippleMode) (control : Wire)
    (ts ads : List Wire) (carry : Wire) (state : BasisState) (w : Wire)
    (ht : w ∉ ts) (ha : w ∉ ads) (hc : w ≠ carry) :
    rippleFirstState mode control ts ads carry state w = state w := by
  induction ts generalizing ads state with
  | nil => rfl
  | cons t ts ih =>
    cases ads with
    | nil => rfl
    | cons a ads =>
      simp only [List.mem_cons, not_or] at ht ha
      rw [rippleFirstState, rippleWrite_outside _ _ _ _ _ _ ht.1 ha.1 hc]
      exact ih ads state ht.2 ha.2

private theorem rippleSecond_outside (mode : RippleMode) (control : Wire)
    (ts ads : List Wire) (carry : Wire) (state : BasisState) (w : Wire)
    (ht : w ∉ ts) (ha : w ∉ ads) (hc : w ≠ carry) :
    rippleSecondState mode control ts ads carry state w = state w := by
  induction ts generalizing ads state with
  | nil => rfl
  | cons t ts ih =>
    cases ads with
    | nil => rfl
    | cons a ads =>
      simp only [List.mem_cons, not_or] at ht ha
      rw [rippleSecondState, ih ads _ ht.2 ha.2,
        rippleWrite_outside _ _ _ _ _ _ ht.1 ha.1 hc]

private theorem rippleLayout_tail (control carry t a : Wire) (ts ads : List Wire)
    (h : (control :: carry :: (t :: ts) ++ (a :: ads)).Nodup) :
    (control :: carry :: ts ++ ads).Nodup := by
  apply List.Sublist.nodup ?_ h
  exact List.Sublist.cons₂ _ (List.Sublist.cons₂ _
    ((List.sublist_cons_self _ _).append (List.sublist_cons_self _ _)))

private theorem rippleWrite_read (t a c : Wire) (bits : RippleCellBits) (state : BasisState)
    (hta : t ≠ a) (htc : t ≠ c) (hac : a ≠ c) :
    readRippleCell t a c (writeRippleCell t a c bits state) = bits := by
  cases bits
  simp [readRippleCell, writeRippleCell, upd, hta, htc, hac]

private theorem rippleWrite_values (t a c : Wire) (bits : RippleCellBits) (state : BasisState)
    (ws : List Wire) (ht : t ∉ ws) (ha : a ∉ ws) (hc : c ∉ ws) :
    wireValues ws (writeRippleCell t a c bits state) = wireValues ws state := by
  apply List.map_congr_left
  intro w hw
  exact rippleWrite_outside _ _ _ _ _ _
    (by intro he; subst w; exact ht hw) (by intro he; subst w; exact ha hw)
    (by intro he; subst w; exact hc hw)

private theorem rippleLayout_parts (control carry t a : Wire) (ts ads : List Wire)
    (h : (control :: carry :: (t :: ts) ++ (a :: ads)).Nodup) :
    control ≠ carry ∧ control ∉ ts ∧ control ∉ ads ∧ t ≠ a ∧ t ≠ carry ∧ a ≠ carry ∧
      t ∉ ts ∧ t ∉ ads ∧ a ∉ ts ∧ a ∉ ads ∧ carry ∉ ts ∧ carry ∉ ads ∧
      control ≠ t ∧ control ≠ a := by
  change (control :: carry :: ((t :: ts) ++ (a :: ads))).Nodup at h
  have hc := (List.nodup_cons.mp h).1
  have hk := (List.nodup_cons.mp (List.nodup_cons.mp h).2).1
  have hb := List.nodup_append.mp (List.nodup_cons.mp (List.nodup_cons.mp h).2).2
  have hcross {w : Wire} (hw : w ∈ t :: ts) : w ∉ a :: ads :=
    fun ha => hb.2.2 w hw w ha rfl
  have hta : t ∉ a :: ads := hcross (by simp)
  have htaParts : t ≠ a ∧ t ∉ ads := by simpa only [List.mem_cons, not_or] using hta
  refine ⟨?_, ?_, ?_, htaParts.1, ?_, ?_, (List.nodup_cons.mp hb.1).1,
    htaParts.2, ?_, (List.nodup_cons.mp hb.2.1).1, ?_, ?_, ?_, ?_⟩
  · intro he; apply hc; simp [he]
  · intro hm; apply hc; simp [hm]
  · intro hm; apply hc; simp [hm]
  · intro he; apply hk; simp [← he]
  · intro he; apply hk; simp [← he]
  · intro hm; exact hcross (List.mem_cons_of_mem t hm) (by simp)
  · intro hm; apply hk; simp [hm]
  · intro hm; apply hk; simp [hm]
  · intro he; apply hc; simp [he]
  · intro he; apply hc; simp [he]

private theorem rippleFirst_words (mode : RippleMode) (control : Wire)
    (ts ads : List Wire) (carry : Wire) (state : BasisState)
    (hnd : (control :: carry :: ts ++ ads).Nodup) (hlen : ts.length = ads.length) :
    (wireValues ts (rippleFirstState mode control ts ads carry state),
      wireValues ads (rippleFirstState mode control ts ads carry state),
      rippleFirstState mode control ts ads carry state carry) =
      rippleWordFirst mode (state control) (wireValues ts state) (wireValues ads state) (state carry) := by
  induction ts generalizing ads state with
  | nil =>
    have ha : ads = [] := List.eq_nil_of_length_eq_zero hlen.symm
    subst ads
    rfl
  | cons t ts ih =>
    cases ads with
    | nil => simp at hlen
    | cons a ads =>
      obtain ⟨hcc, hct, hca, hta, htc, hac, htt, hta', hat, haa, hkt, hka, hct', hca'⟩ :=
        rippleLayout_parts control carry t a ts ads hnd
      have ht : ts.length = ads.length := by simpa using hlen
      let middle := rippleFirstState mode control ts ads carry state
      let cell := rippleFirstBits mode (middle control) (readRippleCell t a carry middle)
      have hm := ih ads state (rippleLayout_tail control carry t a ts ads hnd) ht
      change (wireValues ts middle, wireValues ads middle, middle carry) = _ at hm
      have hmc : middle control = state control := rippleFirst_outside _ _ _ _ _ _ _ hct hca hcc
      have hmt : middle t = state t := rippleFirst_outside _ _ _ _ _ _ _ htt hta' htc
      have hma : middle a = state a := rippleFirst_outside _ _ _ _ _ _ _ hat haa hac
      have hread := rippleWrite_read t a carry cell middle hta htc hac
      have hwT := congrArg RippleCellBits.target hread
      have hwA := congrArg RippleCellBits.addend hread
      have hwC := congrArg RippleCellBits.carry hread
      simp only [readRippleCell] at hwT hwA hwC
      change (writeRippleCell t a carry cell middle t ::
          wireValues ts (writeRippleCell t a carry cell middle),
        writeRippleCell t a carry cell middle a :: wireValues ads (writeRippleCell t a carry cell middle),
        writeRippleCell t a carry cell middle carry) = _
      rw [hwT, hwA, hwC, rippleWrite_values _ _ _ _ _ ts htt hat hkt,
        rippleWrite_values _ _ _ _ _ ads hta' haa hka]
      have hT := congrArg (fun x : List Bool × List Bool × Bool => x.1) hm
      have hA := congrArg (fun x : List Bool × List Bool × Bool => x.2.1) hm
      have hC := congrArg (fun x : List Bool × List Bool × Bool => x.2.2) hm
      simp only at hT hA hC
      dsimp only [cell, readRippleCell]
      rw [hmc, hmt, hma, hT, hA, hC]
      rfl

private theorem rippleSecond_words (mode : RippleMode) (control : Wire)
    (ts ads : List Wire) (carry : Wire) (state : BasisState)
    (hnd : (control :: carry :: ts ++ ads).Nodup) (hlen : ts.length = ads.length) :
    (wireValues ts (rippleSecondState mode control ts ads carry state),
      wireValues ads (rippleSecondState mode control ts ads carry state),
      rippleSecondState mode control ts ads carry state carry) =
      rippleWordSecond mode (state control) (wireValues ts state) (wireValues ads state) (state carry) := by
  induction ts generalizing ads state with
  | nil =>
    have ha : ads = [] := List.eq_nil_of_length_eq_zero hlen.symm
    subst ads
    rfl
  | cons t ts ih =>
    cases ads with
    | nil => simp at hlen
    | cons a ads =>
      obtain ⟨hcc, hct, hca, hta, htc, hac, htt, hta', hat, haa, hkt, hka, hct', hca'⟩ :=
        rippleLayout_parts control carry t a ts ads hnd
      have ht : ts.length = ads.length := by simpa using hlen
      let cell := rippleSecondBits mode (state control) (readRippleCell t a carry state)
      let middle := writeRippleCell t a carry cell state
      let final := rippleSecondState mode control ts ads carry middle
      have hm := ih ads middle (rippleLayout_tail control carry t a ts ads hnd) ht
      change (wireValues ts final, wireValues ads final, final carry) = _ at hm
      have hmc : middle control = state control := rippleWrite_outside _ _ _ _ _ _ hct' hca' hcc
      have hmt : wireValues ts middle = wireValues ts state := rippleWrite_values _ _ _ _ _ ts htt hat hkt
      have hma : wireValues ads middle = wireValues ads state := rippleWrite_values _ _ _ _ _ ads hta' haa hka
      have hread := rippleWrite_read t a carry cell state hta htc hac
      have hwT := congrArg RippleCellBits.target hread
      have hwA := congrArg RippleCellBits.addend hread
      have hwC := congrArg RippleCellBits.carry hread
      change middle t = cell.target at hwT
      change middle a = cell.addend at hwA
      change middle carry = cell.carry at hwC
      have hft : final t = middle t := rippleSecond_outside _ _ _ _ _ _ _ htt hta' htc
      have hfa : final a = middle a := rippleSecond_outside _ _ _ _ _ _ _ hat haa hac
      rw [hmc, hmt, hma, hwC] at hm
      have hT := congrArg (fun x : List Bool × List Bool × Bool => x.1) hm
      have hA := congrArg (fun x : List Bool × List Bool × Bool => x.2.1) hm
      have hC := congrArg (fun x : List Bool × List Bool × Bool => x.2.2) hm
      simp only at hT hA hC
      change (final t :: wireValues ts final, final a :: wireValues ads final, final carry) = _
      rw [hft, hfa, hwT, hwA, hT, hA, hC]
      rfl

private theorem rippleCombined_words (mode : RippleMode) (control : Wire)
    (ts ads : List Wire) (carry : Wire) (state : BasisState)
    (hnd : (control :: carry :: ts ++ ads).Nodup) (hlen : ts.length = ads.length) :
    (wireValues ts (controlledWindowRippleState mode control ts ads carry state),
      wireValues ads (controlledWindowRippleState mode control ts ads carry state),
      controlledWindowRippleState mode control ts ads carry state carry) =
      ((rippleExpected mode (state control) (wireValues ts state) (wireValues ads state) (state carry)).1,
        wireValues ads state, state carry) := by
  let middle := rippleFirstState mode control ts ads carry state
  have hf := rippleFirst_words mode control ts ads carry state hnd hlen
  have hs := rippleSecond_words mode control ts ads carry middle hnd hlen
  change (control :: carry :: (ts ++ ads)).Nodup at hnd
  have hn := (List.nodup_cons.mp hnd).1
  simp only [List.mem_cons, List.mem_append, not_or] at hn
  have hc : middle control = state control := rippleFirst_outside _ _ _ _ _ _ _ hn.2.1 hn.2.2 hn.1
  rw [hc] at hs
  have hT := congrArg (fun x : List Bool × List Bool × Bool => x.1) hf
  have hA := congrArg (fun x : List Bool × List Bool × Bool => x.2.1) hf
  have hC := congrArg (fun x : List Bool × List Bool × Bool => x.2.2) hf
  change wireValues ts middle = _ at hT
  change wireValues ads middle = _ at hA
  change middle carry = _ at hC
  rw [hT, hA, hC] at hs
  have h := (rippleWords_fusion mode (state control) (wireValues ts state) (wireValues ads state)
    (state carry) (by simpa only [wireValues, List.length_map] using hlen)).1
  exact hs.trans h

private theorem rippleRead_member (ws : List Wire) (s t : BasisState)
    (h : wireValues ws s = wireValues ws t) (w : Wire) (hw : w ∈ ws) : s w = t w := by
  induction ws with
  | nil => simp at hw
  | cons x xs ih =>
    simp only [wireValues, List.map_cons, List.cons.injEq] at h
    rcases List.mem_cons.mp hw with rfl | hw
    · exact h.1
    · exact ih h.2 hw

/-- The actual two-pass window ripple performs controlled modular addition or
subtraction on its big-endian target word. Every wire outside that target is
restored, including the addend, arbitrary incoming carry and clean scratch. -/
theorem controlledWindowRipple_arithmetic
    (mode : RippleMode) (control : Wire) (targets addends : List Wire)
    (carry scratch : Wire) (state : BasisState)
    (hlayouts : RippleLaneLayouts control targets addends carry scratch)
    (hdata : (control :: carry :: targets ++ addends).Nodup)
    (hclean : state scratch = false) :
    let after := run (controlledWindowRipple mode control targets addends carry scratch) state
    boolWordToNat (wireValues targets after).reverse =
      (if state control then
        match mode with
        | .add => (boolWordToNat (wireValues targets state).reverse +
            boolWordToNat (wireValues addends state).reverse + (state carry).toNat) % 2^targets.length
        | .sub => (boolWordToNat (wireValues targets state).reverse + 2^targets.length -
            boolWordToNat (wireValues addends state).reverse - (state carry).toNat) % 2^targets.length
       else boolWordToNat (wireValues targets state).reverse) ∧
    (∀ wire, wire ∉ targets → after wire = state wire) := by
  dsimp only
  have hlen : targets.length = addends.length := List.Forall₂.length_eq hlayouts
  rw [run_controlledWindowRipple mode control targets addends carry scratch state hlayouts hclean]
  let after := controlledWindowRippleState mode control targets addends carry state
  have hwords := rippleCombined_words mode control targets addends carry state hdata hlen
  change (wireValues targets after, wireValues addends after, after carry) = _ at hwords
  have ht := congrArg (fun x : List Bool × List Bool × Bool => x.1) hwords
  have ha := congrArg (fun x : List Bool × List Bool × Bool => x.2.1) hwords
  have hc := congrArg (fun x : List Bool × List Bool × Bool => x.2.2) hwords
  simp only at ht ha hc
  constructor
  · change boolWordToNat (wireValues targets after).reverse = _
    rw [ht]
    cases he : state control with
    | false => simp only [rippleExpected_disabled, Bool.false_eq_true, ↓reduceIte]
    | true =>
      simp only [↓reduceIte]
      cases mode with
      | add =>
        simpa only [wireValues, List.length_map] using
          rippleExpected_add_mod (wireValues targets state) (wireValues addends state) (state carry)
            (by simpa only [wireValues, List.length_map] using hlen)
      | sub =>
        simpa only [wireValues, List.length_map] using
          rippleExpected_sub_mod (wireValues targets state) (wireValues addends state) (state carry)
            (by simpa only [wireValues, List.length_map] using hlen)
  · intro wire hw
    change after wire = state wire
    by_cases had : wire ∈ addends
    · exact rippleRead_member addends after state ha wire had
    by_cases he : wire = carry
    · subst wire
      exact hc
    · exact (rippleSecond_outside mode control targets addends carry _ wire hw had he).trans
        (rippleFirst_outside mode control targets addends carry state wire hw had he)

end ShorECDLP.Paper2607_13816
