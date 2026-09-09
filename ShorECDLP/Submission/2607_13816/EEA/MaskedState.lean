import ShorECDLP.Submission.«2607_13816».EEA.MaskedRipple

/-! # Wire-state interpretation of the masked two-pass ripple -/
namespace ShorECDLP.Paper2607_13816
open Classical

def maskedRippleFirstState (mode : RippleMode) :
    List Bool → List Wire → List Wire → Wire → BasisState → BasisState
  | e :: es, t :: ts, a :: ads, carry, state =>
    let middle := maskedRippleFirstState mode es ts ads carry state
    writeRippleCell t a carry (rippleFirstBits mode e (readRippleCell t a carry middle)) middle
  | _, _, _, _, state => state

def maskedRippleSecondState (mode : RippleMode) :
    List Bool → List Wire → List Wire → Wire → BasisState → BasisState
  | e :: es, t :: ts, a :: ads, carry, state =>
    let middle := writeRippleCell t a carry (rippleSecondBits mode e (readRippleCell t a carry state)) state
    maskedRippleSecondState mode es ts ads carry middle
  | _, _, _, _, state => state

private theorem first_outside (mode : RippleMode) (es : List Bool)
    (ts ads : List Wire) (carry : Wire) (state : BasisState) (w : Wire)
    (ht : w ∉ ts) (ha : w ∉ ads) (hc : w ≠ carry) :
    maskedRippleFirstState mode es ts ads carry state w = state w := by
  induction es generalizing ts ads state with
  | nil => rfl
  | cons e es ih =>
    cases ts with
    | nil => rfl
    | cons t ts =>
      cases ads with
      | nil => rfl
      | cons a ads =>
        simp only [List.mem_cons, not_or] at ht ha
        rw [maskedRippleFirstState, rippleWrite_outside _ _ _ _ _ _ ht.1 ha.1 hc]
        exact ih ts ads state ht.2 ha.2

private theorem second_outside (mode : RippleMode) (es : List Bool)
    (ts ads : List Wire) (carry : Wire) (state : BasisState) (w : Wire)
    (ht : w ∉ ts) (ha : w ∉ ads) (hc : w ≠ carry) :
    maskedRippleSecondState mode es ts ads carry state w = state w := by
  induction es generalizing ts ads state with
  | nil => rfl
  | cons e es ih =>
    cases ts with
    | nil => rfl
    | cons t ts =>
      cases ads with
      | nil => rfl
      | cons a ads =>
        simp only [List.mem_cons, not_or] at ht ha
        rw [maskedRippleSecondState, ih ts ads _ ht.2 ha.2,
          rippleWrite_outside _ _ _ _ _ _ ht.1 ha.1 hc]

private theorem layout_tail (carry t a : Wire) (ts ads : List Wire)
    (h : (carry :: (t :: ts) ++ (a :: ads)).Nodup) :
    (carry :: ts ++ ads).Nodup := by
  apply List.Sublist.nodup ?_ h
  exact List.Sublist.cons₂ _
    ((List.sublist_cons_self _ _).append (List.sublist_cons_self _ _))

private theorem layout_parts (carry t a : Wire) (ts ads : List Wire)
    (h : (carry :: (t :: ts) ++ (a :: ads)).Nodup) :
    t ≠ a ∧ t ≠ carry ∧ a ≠ carry ∧ t ∉ ts ∧ t ∉ ads ∧
      a ∉ ts ∧ a ∉ ads ∧ carry ∉ ts ∧ carry ∉ ads := by
  change (carry :: ((t :: ts) ++ (a :: ads))).Nodup at h
  have hk := (List.nodup_cons.mp h).1
  have hb := List.nodup_append.mp (List.nodup_cons.mp h).2
  have hcross {w : Wire} (hw : w ∈ t :: ts) : w ∉ a :: ads :=
    fun ha => hb.2.2 w hw w ha rfl
  have hta : t ∉ a :: ads := hcross (by simp)
  have htaParts : t ≠ a ∧ t ∉ ads := by simpa only [List.mem_cons, not_or] using hta
  refine ⟨htaParts.1, ?_, ?_, (List.nodup_cons.mp hb.1).1, htaParts.2,
    ?_, (List.nodup_cons.mp hb.2.1).1, ?_, ?_⟩
  · intro he; apply hk; simp [← he]
  · intro he; apply hk; simp [← he]
  · intro hm; exact hcross (List.mem_cons_of_mem t hm) (by simp)
  · intro hm; apply hk; simp [hm]
  · intro hm; apply hk; simp [hm]

theorem maskedRippleFirstState_words (mode : RippleMode) (es : List Bool)
    (ts ads : List Wire) (carry : Wire) (state : BasisState)
    (hnd : (carry :: ts ++ ads).Nodup) (he : es.length = ts.length) (hlen : ts.length = ads.length) :
    (wireValues ts (maskedRippleFirstState mode es ts ads carry state),
      wireValues ads (maskedRippleFirstState mode es ts ads carry state),
      maskedRippleFirstState mode es ts ads carry state carry) =
      maskedRippleFirstWords mode es (wireValues ts state) (wireValues ads state) (state carry) := by
  induction es generalizing ts ads state with
  | nil =>
    have ht : ts = [] := List.eq_nil_of_length_eq_zero he.symm
    subst ts
    have ha : ads = [] := List.eq_nil_of_length_eq_zero hlen.symm
    subst ads
    rfl
  | cons e es ih =>
    cases ts with
    | nil => simp at he
    | cons t ts =>
      cases ads with
      | nil => simp at hlen
      | cons a ads =>
        obtain ⟨hta, htc, hac, htt, hta', hat, haa, hkt, hka⟩ :=
          layout_parts carry t a ts ads hnd
        have ht : ts.length = ads.length := by simpa using hlen
        let middle := maskedRippleFirstState mode es ts ads carry state
        let cell := rippleFirstBits mode e (readRippleCell t a carry middle)
        have hm := ih ts ads state (layout_tail carry t a ts ads hnd) (by simpa using he) ht
        change (wireValues ts middle, wireValues ads middle, middle carry) = _ at hm
        have hmt : middle t = state t := first_outside _ _ _ _ _ _ _ htt hta' htc
        have hma : middle a = state a := first_outside _ _ _ _ _ _ _ hat haa hac
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
        rw [hmt, hma, hT, hA, hC]
        rfl



theorem maskedRippleSecondState_words (mode : RippleMode) (es : List Bool)
    (ts ads : List Wire) (carry : Wire) (state : BasisState)
    (hnd : (carry :: ts ++ ads).Nodup) (he : es.length = ts.length) (hlen : ts.length = ads.length) :
    (wireValues ts (maskedRippleSecondState mode es ts ads carry state),
      wireValues ads (maskedRippleSecondState mode es ts ads carry state),
      maskedRippleSecondState mode es ts ads carry state carry) =
      maskedRippleSecondWords mode es (wireValues ts state) (wireValues ads state) (state carry) := by
  induction es generalizing ts ads state with
  | nil =>
    have ht : ts = [] := List.eq_nil_of_length_eq_zero he.symm
    subst ts
    have ha : ads = [] := List.eq_nil_of_length_eq_zero hlen.symm
    subst ads
    rfl
  | cons e es ih =>
    cases ts with
    | nil => simp at he
    | cons t ts =>
      cases ads with
      | nil => simp at hlen
      | cons a ads =>
        obtain ⟨hta, htc, hac, htt, hta', hat, haa, hkt, hka⟩ :=
          layout_parts carry t a ts ads hnd
        have ht : ts.length = ads.length := by simpa using hlen
        let cell := rippleSecondBits mode e (readRippleCell t a carry state)
        let middle := writeRippleCell t a carry cell state
        let final := maskedRippleSecondState mode es ts ads carry middle
        have hm := ih ts ads middle (layout_tail carry t a ts ads hnd) (by simpa using he) ht
        change (wireValues ts final, wireValues ads final, final carry) = _ at hm
        have hmt : wireValues ts middle = wireValues ts state := rippleWrite_values _ _ _ _ _ ts htt hat hkt
        have hma : wireValues ads middle = wireValues ads state := rippleWrite_values _ _ _ _ _ ads hta' haa hka
        have hread := rippleWrite_read t a carry cell state hta htc hac
        have hwT := congrArg RippleCellBits.target hread
        have hwA := congrArg RippleCellBits.addend hread
        have hwC := congrArg RippleCellBits.carry hread
        change middle t = cell.target at hwT
        change middle a = cell.addend at hwA
        change middle carry = cell.carry at hwC
        have hft : final t = middle t := second_outside _ _ _ _ _ _ _ htt hta' htc
        have hfa : final a = middle a := second_outside _ _ _ _ _ _ _ hat haa hac
        rw [hmt, hma, hwC] at hm
        have hT := congrArg (fun x : List Bool × List Bool × Bool => x.1) hm
        have hA := congrArg (fun x : List Bool × List Bool × Bool => x.2.1) hm
        have hC := congrArg (fun x : List Bool × List Bool × Bool => x.2.2) hm
        simp only at hT hA hC
        change (final t :: wireValues ts final, final a :: wireValues ads final, final carry) = _
        rw [hft, hfa, hwT, hwA, hT, hA, hC]
        rfl



/-- Both wire-state passes have the fused word values and restore every wire outside
of the target list, including the entire addend and the arbitrary incoming carry. -/
theorem maskedRippleState_fusion (mode : RippleMode) (es : List Bool)
    (ts ads : List Wire) (carry : Wire) (state : BasisState)
    (hnd : (carry :: ts ++ ads).Nodup) (he : es.length = ts.length)
    (hlen : ts.length = ads.length) :
    let first := maskedRippleFirstState mode es ts ads carry state
    let final := maskedRippleSecondState mode es ts ads carry first
    (wireValues ts final, wireValues ads final, final carry) =
      ((maskedRippleExpectedWords mode es (wireValues ts state) (wireValues ads state) (state carry)).1,
        wireValues ads state, state carry) ∧
      (∀ w, w ∉ ts → final w = state w) := by
  let first := maskedRippleFirstState mode es ts ads carry state
  let final := maskedRippleSecondState mode es ts ads carry first
  have hf := maskedRippleFirstState_words mode es ts ads carry state hnd he hlen
  have hs := maskedRippleSecondState_words mode es ts ads carry first hnd he hlen
  have hT := congrArg (fun x : List Bool × List Bool × Bool => x.1) hf
  have hA := congrArg (fun x : List Bool × List Bool × Bool => x.2.1) hf
  have hC := congrArg (fun x : List Bool × List Bool × Bool => x.2.2) hf
  change wireValues ts first = _ at hT
  change wireValues ads first = _ at hA
  change first carry = _ at hC
  rw [hT, hA, hC] at hs
  have hw := (maskedRippleWords_fusion mode es (wireValues ts state) (wireValues ads state)
    (state carry) (by simpa only [wireValues, List.length_map] using he)
    (by simpa only [wireValues, List.length_map] using hlen)).1
  have hwords := hs.trans hw
  refine ⟨hwords, ?_⟩
  intro w hwt
  by_cases hwa : w ∈ ads
  · exact rippleRead_member ads final state
      (congrArg (fun x : List Bool × List Bool × Bool => x.2.1) hwords) w hwa
  · by_cases hwc : w = carry
    · subst w
      exact congrArg (fun x : List Bool × List Bool × Bool => x.2.2) hwords
    · exact (second_outside mode es ts ads carry first w hwt hwa hwc).trans
        (first_outside mode es ts ads carry state w hwt hwa hwc)

end ShorECDLP.Paper2607_13816
