import ShorECDLP.Submission.«2607_13816».EEA.BlockBArithmetic

/-! # Conditional subtraction performed by the complete source Block B -/
namespace ShorECDLP.Paper2607_13816
open Classical
private def preservedWires (r : IndexedStepRegisters) : List Wire :=
  [r.phase1,r.phase2,r.iter] ++ r.work2 ++ r.lengthT ++ r.lengthQ ++ r.lengthS ++ r.lengthRPrime ++ r.aux
private theorem preserved_not_changes (r : IndexedStepRegisters) (n index : Nat)
    (h : IndexedStepLayout r n index) (wire : Wire) (hw : wire ∈ preservedWires r) :
    wire ∉ r.sign :: r.work1 := by
  let phaseWires := [r.phase1,r.phase2,r.iter]
  let rest := r.work2 ++ r.lengthT ++ r.lengthQ ++ r.lengthS ++ r.lengthRPrime ++ r.aux
  have hp : ((phaseWires ++ [r.sign]) ++ (r.work1 ++ rest)).Nodup := by
    simpa only [phaseWires,rest,IndexedStepRegisters.allWires,List.append_assoc] using h.physical
  have hh := (List.nodup_append.mp (List.nodup_append.mp hp).1).2.2
  have ht := (List.nodup_append.mp hp).2.2
  have hr := (List.nodup_append.mp (List.nodup_append.mp hp).2.1).2.2
  have hm : wire ∈ phaseWires ++ rest := by
    simpa only [phaseWires,rest,preservedWires,List.append_assoc] using hw
  intro hn
  rcases List.mem_cons.mp hn with hs | hs
  · subst wire
    rcases List.mem_append.mp hm with hm | hm
    · exact hh r.sign hm r.sign (by simp) rfl
    · exact ht r.sign (by simp) r.sign (List.mem_append_right _ hm) rfl
  · rcases List.mem_append.mp hm with hm | hm
    · exact ht wire (List.mem_append_left _ hm) wire (List.mem_append_left _ hs) rfl
    · exact hr wire hs wire hm rfl

private theorem work1_ne_sign (r : IndexedStepRegisters) (n index : Nat)
    (h : IndexedStepLayout r n index) (wire : Wire) (hw : wire ∈ r.work1) : wire ≠ r.sign := by
  have hphys := h.physical
  simp only [IndexedStepRegisters.allWires,List.append_assoc] at hphys
  have hp := (List.nodup_append.mp hphys).2.2
  intro he
  subst wire
  exact hp r.sign (by simp) r.sign (List.mem_append_left _ hw) rfl

private theorem fieldValue_lt (ws : List Wire) (state : BasisState) (start width : Nat) :
    boolWordToNat (((wireValues ws state).drop start).take width).reverse < 2^width := by
  have hb := boolWordToNat_lt_pow_two (((wireValues ws state).drop start).take width).reverse
  have hl : ((((wireValues ws state).drop start).take width).reverse).length ≤ width := by simp
  exact hb.trans_le (Nat.pow_le_pow_right (by decide) hl)
private theorem and_congr (ws : List Wire) (s t : BasisState)
    (h : ∀ wire ∈ ws, s wire = t wire) : wireAnd ws s = wireAnd ws t := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [wireAnd,h w (by simp),ih (fun wire hw => h wire (by simp [hw]))]

private theorem control_zero (r : IndexedStepRegisters) (n index : Nat)
    (h : IndexedStepLayout r n index) (state : BasisState) (hc : Clean r.aux state) : state r.control = false := by
  apply hc
  change r.aux.getD 0 0 ∈ r.aux
  rw [List.getD_eq_getElem r.aux 0 (by rw [h.aux_length]; decide)]
  exact List.getElem_mem _

private theorem blockB3_sign (r : IndexedStepRegisters) (n index : Nat)
    (state : BasisState) (h : IndexedStepLayout r n index) (hc : Clean r.aux state) :
    run (blockB3Forward r n (certifiedActiveWindows n index).remainder) state r.sign = state r.sign := by
  let w := (certifiedActiveWindows n index).remainder
  have hf := run_blockB3Forward_interval r n index state h hc
  have hcs : r.control ≠ r.sign := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using (List.nodup_cons.mp h.controlSign).1
  have hi := intervalAddSubUnitary_preserves_sign_of_false (r.remainder w) n w.start w.stop .add .work1
    state[r.control ↦ (!state r.phase1 && !(state r.phase2 && state r.sign) && !wireAnd r.lengthRPrime state)] h.remainder hf.2.1
  have he : (r.remainder w).sign = r.sign := rfl
  rw [he] at hi
  rw [hf.1]
  simpa only [upd,hcs.symm,if_false] using hi

private theorem blockB3_idle (r : IndexedStepRegisters) (n index : Nat)
    (state : BasisState) (h : IndexedStepLayout r n index) (hc : Clean r.aux state)
    (hp : (!state r.phase1 && !(state r.phase2 && state r.sign) && !wireAnd r.lengthRPrime state) = false) :
    run (blockB3Forward r n (certifiedActiveWindows n index).remainder) state = state := by
  let w := (certifiedActiveWindows n index).remainder
  have hf := run_blockB3Forward_interval r n index state h hc
  have hz := control_zero r n index h state hc
  have hu : state[r.control ↦ false] = state := by
    funext wire
    by_cases he : wire = r.control
    · subst wire; simp [upd,hz]
    · simp [upd,he]
  have he : state[r.control ↦ (!state r.phase1 && !(state r.phase2 && state r.sign) && !wireAnd r.lengthRPrime state)] = state := by rw [hp,hu]
  have hr : IntervalReady (r.remainder w) state := by simpa only [he] using hf.2.1
  rw [hf.1,he,intervalAddSubUnitary_idle (r.remainder w) n w.start w.stop .add false .work1 state h.remainder hr hz,hu]

/-- Actual Block B performs the active-phase comparison or conditional subtraction
on the aligned divisor field, and restores its auxiliary bank. -/
theorem blockBForward_activeArithmetic (r : IndexedStepRegisters) (n index ellT ellQ shift : Nat)
    (state : BasisState) (h : IndexedStepLayout r n index) (hc : Clean r.aux state)
    (hphase : state r.phase1 = false) (hsign0 : state r.sign = false)
    (hrp : wireAnd r.lengthRPrime state = false)
    (ht : boolWordToNat (wireValues r.lengthT state) = truthMinusOneValue r.lengthQ.length ellT)
    (hq : boolWordToNat (wireValues r.lengthQ state) = truthMinusOneValue r.lengthQ.length ellQ)
    (hs : boolWordToNat (wireValues r.lengthS state) = truthMinusOneValue r.lengthS.length shift)
    (hleftLow : (certifiedActiveWindows n index).remainder.start ≤ ellT+ellQ+2)
    (hleftHigh : ellT+ellQ+2-(certifiedActiveWindows n index).remainder.start < 2^r.lengthQ.length)
    (hrightLow : shift+(certifiedActiveWindows n index).remainder.start ≤ n+3)
    (hrightHigh : n+3-shift-(certifiedActiveWindows n index).remainder.start < 2^r.lengthS.length)
    (horder : ellT+ellQ+2-(certifiedActiveWindows n index).remainder.start ≤
      n+3-shift-(certifiedActiveWindows n index).remainder.start) :
    let w := (certifiedActiveWindows n index).remainder
    let width := n+3-shift-(ellT+ellQ+2)+1
    let value := fun ws s => boolWordToNat ((((wireValues ws s).drop (ellT+ellQ+1)).take width).reverse)
    value r.work1 (run (blockBForward r n w) state) =
      (if state r.phase2 && decide (value r.work2 state ≤ value r.work1 state) then
        value r.work1 state - value r.work2 state else value r.work1 state) ∧
    run (blockBForward r n w) state r.sign = (decide (value r.work1 state < value r.work2 state) ^^ state r.phase2) ∧
    Clean r.aux (run (blockBForward r n w) state) := by
  let w := (certifiedActiveWindows n index).remainder
  let width := n+3-shift-(ellT+ellQ+2)+1
  let value := fun ws s => boolWordToNat ((((wireValues ws s).drop (ellT+ellQ+1)).take width).reverse)
  let x := value r.work1 state
  let y := value r.work2 state
  let first := run (blockB1Forward r n w) state
  let second := run (blockB2 r) first
  have hnum := blockB1Forward_logicalValues r n index ellT ellQ shift state h hc hphase hrp ht hq hs
    hleftLow hleftHigh hrightLow hrightHigh horder
  have hborrow := blockB1Forward_logicalBorrow r n index ellT ellQ shift state h hc hphase hrp ht hq hs
    hleftLow hleftHigh hrightLow hrightHigh horder
  have h2 := run_blockB2_sign r n index first h hnum.2
  have hframe := blockB1Forward_frame r n index state h hc
  have hfirst (wire : Wire) (hw : wire ∈ preservedWires r) : first wire = state wire :=
    hframe wire (preserved_not_changes r n index h wire hw)
  have hsecond (wire : Wire) (hw : wire ∈ preservedWires r) : second wire = state wire := by
    have hn : wire ≠ r.sign := fun he => preserved_not_changes r n index h wire hw (by simp [he])
    have hh := congrFun h2.1 wire
    simpa only [upd,hn,if_false,hfirst wire hw] using hh
  have hwords (ws : List Wire) (hw : ∀ wire ∈ ws, wire ∈ preservedWires r) :
      wireValues ws second = wireValues ws state := by
    apply List.map_congr_left
    intro wire hm
    exact hsecond wire (hw wire hm)
  have hp1 : first r.phase1 = false := (hfirst _ (by simp [preservedWires])).trans hphase
  have hp2 : first r.phase2 = state r.phase2 := hfirst _ (by simp [preservedWires])
  have hR1 : wireAnd r.lengthRPrime first = false :=
    (and_congr _ first state (fun wire hw => hfirst wire (by simp [preservedWires,hw]))).trans hrp
  have hb : first r.sign = decide (x < y) := by
    simpa only [hsign0,Bool.false_xor] using hborrow.1
  have hsign2 : second r.sign = (decide (x < y) ^^ state r.phase2) := by
    simpa [upd,hb,hp1,hp2,hR1] using congrFun h2.1 r.sign
  have hp12 : second r.phase1 = false := (hsecond _ (by simp [preservedWires])).trans hphase
  have hp22 : second r.phase2 = state r.phase2 := hsecond _ (by simp [preservedWires])
  have hR2 : wireAnd r.lengthRPrime second = false :=
    (and_congr _ second state (fun wire hw => hsecond wire (by simp [preservedWires,hw]))).trans hrp
  have hT := hwords r.lengthT (by intro wire hw; simp [preservedWires,hw])
  have hQ := hwords r.lengthQ (by intro wire hw; simp [preservedWires,hw])
  have hS := hwords r.lengthS (by intro wire hw; simp [preservedWires,hw])
  have hW2 := hwords r.work2 (by intro wire hw; simp [preservedWires,hw])
  have hW1 : wireValues r.work1 second = wireValues r.work1 first := by
    apply List.map_congr_left
    intro wire hw
    simpa only [upd,work1_ne_sign r n index h wire hw,if_false] using congrFun h2.1 wire
  have hx2 : value r.work1 second = (x+2^width-y)%2^width := by
    dsimp only [value]
    rw [hW1]
    exact hnum.1
  have hy2 : value r.work2 second = y := by dsimp only [value]; rw [hW2]
  have hshape : run (blockBForward r n w) state = run (blockB3Forward r n w) second := by
    simp only [blockBForward,first,second,Classical.run_append]
  have h3 := run_blockB3Forward_interval r n index second h h2.2
  have hsign : run (blockBForward r n w) state r.sign = (decide (x < y) ^^ state r.phase2) := by
    rw [hshape,blockB3_sign r n index second h h2.2,hsign2]
  have hxb : x < 2^width := fieldValue_lt r.work1 state _ _
  have hyb : y < 2^width := fieldValue_lt r.work2 state _ _
  have haddback (hrestore : (second r.phase2 && second r.sign) = false) :
      value r.work1 (run (blockB3Forward r n w) second) = x := by
    have ha := blockB3Forward_logicalValues r n index ellT ellQ shift second h h2.2 hp12 hR2 hrestore
      (by simpa only [hT] using ht) (by simpa only [hQ] using hq) (by simpa only [hS] using hs)
      hleftLow hleftHigh hrightLow hrightHigh horder
    have hav : value r.work1 (run (blockB3Forward r n w) second) =
        (value r.work1 second + value r.work2 second)%2^width := ha.1
    rw [hx2,hy2,Nat.mod_add_mod,show x+2^width-y+y = x+2^width by omega,
      Nat.add_mod_right,Nat.mod_eq_of_lt hxb] at hav
    exact hav
  dsimp only
  refine ⟨?_,hsign,?_⟩
  · change value r.work1 (run (blockBForward r n w) state) =
      if state r.phase2 && decide (y ≤ x) then x-y else x
    rw [hshape]
    cases hphase2 : state r.phase2 with
    | false =>
      have ha := haddback (by simp [hp22,hphase2])
      simpa only [hphase2,Bool.false_and,Bool.false_eq_true,if_false] using ha
    | true =>
      by_cases hlt : x < y
      · have ha := haddback (by simp [hp22,hsign2,hphase2,hlt])
        simpa only [hphase2,decide_eq_false (Nat.not_le.mpr hlt),Bool.and_false,Bool.false_eq_true,if_false] using ha
      · have hdisable : (!second r.phase1 && !(second r.phase2 && second r.sign) && !wireAnd r.lengthRPrime second) = false := by
          simp [hp12,hp22,hsign2,hR2,hphase2,hlt]
        rw [blockB3_idle r n index second h h2.2 hdisable,hx2]
        simp only [decide_eq_true (Nat.le_of_not_gt hlt),Bool.and_true,if_true]
        rw [show x+2^width-y = x-y+2^width by omega,Nat.add_mod_right,
          Nat.mod_eq_of_lt (show x-y < 2^width by omega)]
  · rw [hshape]
    exact h3.2.2

end ShorECDLP.Paper2607_13816
