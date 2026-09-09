import ShorECDLP.Submission.«2607_13816».EEA.RemainderWindow

/-! # Arithmetic of the source remainder subtraction block -/
namespace ShorECDLP.Paper2607_13816
open Classical
private def dataWires (r : IndexedStepRegisters) : List Wire :=
  r.work1 ++ r.work2 ++ r.lengthT ++ r.lengthQ ++ r.lengthS

private theorem data_ne_control (r : IndexedStepRegisters) (n index : Nat)
    (h : IndexedStepLayout r n index) (wire : Wire) (hw : wire ∈ dataWires r) : wire ≠ r.control := by
  have hc : r.control ∈ r.aux := by
    change r.aux.getD 0 0 ∈ r.aux
    rw [List.getD_eq_getElem r.aux 0 (by rw [h.aux_length]; decide)]
    exact List.getElem_mem _
  let payload := [r.phase1,r.phase2,r.iter,r.sign] ++ (dataWires r ++ r.lengthRPrime)
  have hp : (payload ++ r.aux).Nodup := by
    simpa only [payload,dataWires,IndexedStepRegisters.allWires,List.append_assoc] using h.physical
  intro he
  exact (List.nodup_append.mp hp).2.2 wire
    (List.mem_append_right _ (List.mem_append_left _ hw)) r.control hc he

private theorem data_words_update (r : IndexedStepRegisters) (n index : Nat)
    (h : IndexedStepLayout r n index) (ws : List Wire) (hm : ∀ w ∈ ws, w ∈ dataWires r)
    (state : BasisState) (value : Bool) :
    wireValues ws state[r.control ↦ value] = wireValues ws state := by
  apply List.map_congr_left
  intro w hw
  simp only [upd,data_ne_control r n index h w (hm w hw),if_false]

private theorem subtraction_enabled (r : IndexedStepRegisters) (n index : Nat)
    (h : IndexedStepLayout r n index) (state : BasisState)
    (hp : state r.phase1 = false) (hr : wireAnd r.lengthRPrime state = false) :
    rControlNonterminalPredicate [r.phase1] 0 r.lengthRPrime r.terminal state = true := by
  rw [rControlNonterminalPredicate_eq _ _ _ _ _ (List.nodup_cons.mp h.terminalPhase).1]
  simp [registerMatches,registerMatchesFrom,hp,hr]


/-- In the active remainder phase, actual Block B1 subtracts the aligned work2
field from work1 modulo its width and returns the entire auxiliary bank clean.
Logical encoding and endpoint bounds remain explicit reachable-state obligations. -/
theorem blockB1Forward_logicalValues (r : IndexedStepRegisters) (n index ellT ellQ shift : Nat)
    (state : BasisState) (h : IndexedStepLayout r n index) (hc : Clean r.aux state)
    (hphase : state r.phase1 = false) (hrp : wireAnd r.lengthRPrime state = false)
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
    value r.work1 (run (blockB1Forward r n w) state) =
      (value r.work1 state + 2^width - value r.work2 state) % 2^width ∧
    Clean r.aux (run (blockB1Forward r n w) state) := by
  let w := (certifiedActiveWindows n index).remainder
  let enabled := state[r.control ↦ rControlNonterminalPredicate [r.phase1] 0 r.lengthRPrime r.terminal state]
  let changed := run (intervalAddSubUnitary (r.remainder w) n w.start w.stop .sub true .work1) enabled
  have hf := run_blockB1Forward_interval r n index state h hc
  have hp := subtraction_enabled r n index h state hphase hrp
  have he : enabled r.control = true := by simp [enabled,hp]
  have hdata (ws : List Wire) (hm : ∀ wire ∈ ws, wire ∈ dataWires r) :
      wireValues ws enabled = wireValues ws state := data_words_update r n index h ws hm state _
  have hT := hdata r.lengthT (by intro wire hw; simp [dataWires,hw])
  have hQ := hdata r.lengthQ (by intro wire hw; simp [dataWires,hw])
  have hS := hdata r.lengthS (by intro wire hw; simp [dataWires,hw])
  have hW1 := hdata r.work1 (by intro wire hw; simp [dataWires,hw])
  have hW2 := hdata r.work2 (by intro wire hw; simp [dataWires,hw])
  have hout := data_words_update r n index h r.work1 (by intro wire hw; simp [dataWires,hw]) changed false
  have hstart : 1 ≤ w.start := by simp only [w,certifiedActiveWindows,certifiedRemainderWindow]; omega
  have hrange : n+3-shift-w.start ≤ intervalTopRelative w.start w.stop := by
    simp only [intervalTopRelative,intervalLaneCount,w,certifiedActiveWindows,certifiedRemainderWindow]
    omega
  have hb := run_remainderInterval_logicalValues r w n ellT ellQ shift .sub true .work1 enabled h.remainder
    hstart hf.2.1 he (by simpa only [hT] using ht) (by simpa only [hQ] using hq) (by simpa only [hS] using hs)
    hleftLow hleftHigh hrightLow hrightHigh hrange horder
  dsimp only at hb ⊢
  rw [hW1,hW2] at hb
  constructor
  · rw [hf.1,hout]
    exact hb
  · exact hf.2.2
/-- When the restore predicate is active, actual Block B3 adds the aligned work2
field to work1 modulo its width and returns the entire auxiliary bank clean.
Logical encoding and endpoint bounds remain explicit reachable-state obligations. -/
theorem blockB3Forward_logicalValues (r : IndexedStepRegisters) (n index ellT ellQ shift : Nat)
    (state : BasisState) (h : IndexedStepLayout r n index) (hc : Clean r.aux state)
    (hphase : state r.phase1 = false) (hrp : wireAnd r.lengthRPrime state = false)
    (hrestore : (state r.phase2 && state r.sign) = false)
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
    value r.work1 (run (blockB3Forward r n w) state) =
      (value r.work1 state + value r.work2 state) % 2^width ∧
    Clean r.aux (run (blockB3Forward r n w) state) := by
  let w := (certifiedActiveWindows n index).remainder
  let enabled := state[r.control ↦ (!state r.phase1 && !(state r.phase2 && state r.sign) && !wireAnd r.lengthRPrime state)]
  let changed := run (intervalAddSubUnitary (r.remainder w) n w.start w.stop .add false .work1) enabled
  have hf := run_blockB3Forward_interval r n index state h hc
  have he : enabled r.control = true := by simp [enabled,hphase,hrp,hrestore]
  have hdata (ws : List Wire) (hm : ∀ wire ∈ ws, wire ∈ dataWires r) :
      wireValues ws enabled = wireValues ws state := data_words_update r n index h ws hm state _
  have hT := hdata r.lengthT (by intro wire hw; simp [dataWires,hw])
  have hQ := hdata r.lengthQ (by intro wire hw; simp [dataWires,hw])
  have hS := hdata r.lengthS (by intro wire hw; simp [dataWires,hw])
  have hW1 := hdata r.work1 (by intro wire hw; simp [dataWires,hw])
  have hW2 := hdata r.work2 (by intro wire hw; simp [dataWires,hw])
  have hout := data_words_update r n index h r.work1 (by intro wire hw; simp [dataWires,hw]) changed false
  have hstart : 1 ≤ w.start := by simp only [w,certifiedActiveWindows,certifiedRemainderWindow]; omega
  have hrange : n+3-shift-w.start ≤ intervalTopRelative w.start w.stop := by
    simp only [intervalTopRelative,intervalLaneCount,w,certifiedActiveWindows,certifiedRemainderWindow]
    omega
  have hb := run_remainderInterval_logicalValues r w n ellT ellQ shift .add false .work1 enabled h.remainder
    hstart hf.2.1 he (by simpa only [hT] using ht) (by simpa only [hQ] using hq) (by simpa only [hS] using hs)
    hleftLow hleftHigh hrightLow hrightHigh hrange horder
  dsimp only at hb ⊢
  rw [hW1,hW2] at hb
  constructor
  · rw [hf.1,hout]
    exact hb
  · exact hf.2.2
/-- The complete actual Block B consists of subtraction, a phase-two sign flip,
and conditional addback, with controls and the auxiliary bank cleaned. Both
arithmetic calls below are the source interval circuits. -/
theorem run_blockBForward_intervals (r : IndexedStepRegisters) (n index : Nat)
    (state : BasisState) (h : IndexedStepLayout r n index) (hc : Clean r.aux state) :
    let w := (certifiedActiveWindows n index).remainder
    let first := (run (intervalAddSubUnitary (r.remainder w) n w.start w.stop .sub true .work1)
      state[r.control ↦ rControlNonterminalPredicate [r.phase1] 0 r.lengthRPrime r.terminal state])[r.control ↦ false]
    let second := first[r.sign ↦ (first r.sign ^^ (!first r.phase1 && first r.phase2 && !wireAnd r.lengthRPrime first))]
    let third := run (intervalAddSubUnitary (r.remainder w) n w.start w.stop .add false .work1)
      second[r.control ↦ (!second r.phase1 && !(second r.phase2 && second r.sign) && !wireAnd r.lengthRPrime second)]
    run (blockBForward r n w) state = third[r.control ↦ false] ∧
      Clean r.aux (run (blockBForward r n w) state) := by
  let w := (certifiedActiveWindows n index).remainder
  have h1 := run_blockB1Forward_interval r n index state h hc
  have h2 := run_blockB2_sign r n index (run (blockB1Forward r n w) state) h h1.2.2
  have h3 := run_blockB3Forward_interval r n index
    (run (blockB2 r) (run (blockB1Forward r n w) state)) h h2.2
  constructor
  · simp only [blockBForward,Classical.run_append]
    rw [h3.1,h2.1,h1.1]
  · simpa only [blockBForward,Classical.run_append] using h3.2.2

/-- Actual B1 records unsigned borrow of the aligned work-bank field in sign. -/
theorem blockB1Forward_logicalBorrow (r : IndexedStepRegisters) (n index ellT ellQ shift : Nat)
    (state : BasisState) (h : IndexedStepLayout r n index) (hc : Clean r.aux state)
    (hphase : state r.phase1 = false) (hrp : wireAnd r.lengthRPrime state = false)
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
    run (blockB1Forward r n w) state r.sign =
      (state r.sign ^^ decide (value r.work1 state < value r.work2 state)) ∧
    Clean r.aux (run (blockB1Forward r n w) state) := by
  let w := (certifiedActiveWindows n index).remainder
  let enabled := state[r.control ↦ rControlNonterminalPredicate [r.phase1] 0 r.lengthRPrime r.terminal state]
  let changed := run (intervalAddSubUnitary (r.remainder w) n w.start w.stop .sub true .work1) enabled
  have hf := run_blockB1Forward_interval r n index state h hc
  have hp := subtraction_enabled r n index h state hphase hrp
  have he : enabled r.control = true := by simp [enabled,hp]
  have hdata (ws : List Wire) (hm : ∀ wire ∈ ws, wire ∈ dataWires r) :
      wireValues ws enabled = wireValues ws state := data_words_update r n index h ws hm state _
  have hT := hdata r.lengthT (by intro wire hw; simp [dataWires,hw])
  have hQ := hdata r.lengthQ (by intro wire hw; simp [dataWires,hw])
  have hS := hdata r.lengthS (by intro wire hw; simp [dataWires,hw])
  have hW1 := hdata r.work1 (by intro wire hw; simp [dataWires,hw])
  have hW2 := hdata r.work2 (by intro wire hw; simp [dataWires,hw])
  have hcs : r.control ≠ r.sign := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using (List.nodup_cons.mp h.controlSign).1
  have hSign : enabled r.sign = state r.sign := by simp [enabled,upd,hcs.symm]
  have hout : changed[r.control ↦ false] r.sign = changed r.sign := by simp [upd,hcs.symm]
  have hstart : 1 ≤ w.start := by simp only [w,certifiedActiveWindows,certifiedRemainderWindow]; omega
  have hrange : n+3-shift-w.start ≤ intervalTopRelative w.start w.stop := by
    simp only [intervalTopRelative,intervalLaneCount,w,certifiedActiveWindows,certifiedRemainderWindow]
    omega
  have hb := run_remainderInterval_logicalBorrow r w n ellT ellQ shift .work1 enabled h.remainder
    hstart hf.2.1 he (by simpa only [hT] using ht) (by simpa only [hQ] using hq) (by simpa only [hS] using hs)
    hleftLow hleftHigh hrightLow hrightHigh hrange horder
  dsimp only at hb ⊢
  rw [hW1,hW2,hSign] at hb
  constructor
  · rw [hf.1,hout]
    exact hb
  · exact hf.2.2
private theorem controlledInterval_frame (r : IndexedStepRegisters) (n index : Nat)
    (mode : RippleMode) (signUpdate value : Bool) (state : BasisState)
    (h : IndexedStepLayout r n index) (hc : Clean r.aux state)
    (hr : IntervalReady (r.remainder (certifiedActiveWindows n index).remainder)
      state[r.control ↦ value]) :
    let w := (certifiedActiveWindows n index).remainder
    AgreesOutside (r.sign :: r.work1)
      (run (intervalAddSubUnitary (r.remainder w) n w.start w.stop mode signUpdate .work1)
        state[r.control ↦ value])[r.control ↦ false] state := by
  let w := (certifiedActiveWindows n index).remainder
  have hi := intervalAddSubUnitary_preservesOutsideTarget (r.remainder w) n w.start w.stop mode signUpdate .work1
    state[r.control ↦ value] h.remainder hr
  have hcontrol : state r.control = false := by
    apply hc
    change r.aux.getD 0 0 ∈ r.aux
    rw [List.getD_eq_getElem r.aux 0 (by rw [h.aux_length]; decide)]
    exact List.getElem_mem _
  dsimp only
  intro wire hn
  by_cases he : wire = r.control
  · subst wire
    simp [upd,hcontrol]
  · have hv : wire ∉ (r.remainder w).sign :: (r.remainder w).work1 := by
      change wire ∉ r.sign :: IndexedStepRegisters.windowSlice r.work1 w
      intro hw
      rcases List.mem_cons.mp hw with hw | hw
      · exact hn (List.mem_cons.mpr (Or.inl hw))
      · exact hn (List.mem_cons.mpr (Or.inr (List.mem_of_mem_drop (List.mem_of_mem_take hw))))
    have hb := hi wire (by simpa only [if_pos rfl] using hv)
    simpa only [upd,he,if_false] using hb

/-- Actual B1 preserves the addend, all metadata, and every other wire outside
its target work bank and sign. -/
theorem blockB1Forward_frame (r : IndexedStepRegisters) (n index : Nat)
    (state : BasisState) (h : IndexedStepLayout r n index) (hc : Clean r.aux state) :
    AgreesOutside (r.sign :: r.work1)
      (run (blockB1Forward r n (certifiedActiveWindows n index).remainder) state) state := by
  have hb := run_blockB1Forward_interval r n index state h hc
  rw [hb.1]
  exact controlledInterval_frame r n index .sub true _ state h hc hb.2.1

private theorem blockB3Forward_frame (r : IndexedStepRegisters) (n index : Nat)
    (state : BasisState) (h : IndexedStepLayout r n index) (hc : Clean r.aux state) :
    AgreesOutside (r.sign :: r.work1)
      (run (blockB3Forward r n (certifiedActiveWindows n index).remainder) state) state := by
  have hb := run_blockB3Forward_interval r n index state h hc
  rw [hb.1]
  exact controlledInterval_frame r n index .add false _ state h hc hb.2.1

/-- The full source Block B restores all metadata and the addend work bank;
only work1 and sign can change. -/
theorem blockBForward_frame (r : IndexedStepRegisters) (n index : Nat)
    (state : BasisState) (h : IndexedStepLayout r n index) (hc : Clean r.aux state) :
    AgreesOutside (r.sign :: r.work1)
      (run (blockBForward r n (certifiedActiveWindows n index).remainder) state) state := by
  let w := (certifiedActiveWindows n index).remainder
  let first := run (blockB1Forward r n w) state
  let second := run (blockB2 r) first
  have h1 := run_blockB1Forward_interval r n index state h hc
  have h2 := run_blockB2_sign r n index first h h1.2.2
  have hf := blockB1Forward_frame r n index state h hc
  have h3 := blockB3Forward_frame r n index second h h2.2
  intro wire hn
  have hsign : wire ≠ r.sign := fun he => hn (List.mem_cons.mpr (Or.inl he))
  have hs : second wire = first wire := by simpa only [upd,hsign,if_false] using congrFun h2.1 wire
  simpa only [blockBForward,Classical.run_append] using (h3 wire hn).trans (hs.trans (hf wire hn))

/-- On clean nonterminal inputs, terminal restoration after Block B preserves
its complete output, so every canonical remainder contract carries through C. -/
theorem blockBCForward_eq_blockB (r : IndexedStepRegisters) (n index : Nat)
    (state : BasisState) (h : IndexedStepLayout r n index) (hc : Clean r.aux state)
    (hrp : wireAnd r.lengthRPrime state = false) :
    run (blockBForward r n (certifiedActiveWindows n index).remainder ++ blockCForward r) state =
      run (blockBForward r n (certifiedActiveWindows n index).remainder) state := by
  let final := run (blockBForward r n (certifiedActiveWindows n index).remainder) state
  have hf := blockBForward_frame r n index state h hc
  let pre := [r.phase1,r.phase2,r.iter,r.sign] ++ r.work1 ++ r.work2 ++ r.lengthT ++ r.lengthQ ++ r.lengthS
  have hp : (pre ++ (r.lengthRPrime ++ r.aux)).Nodup := by
    simpa only [pre,IndexedStepRegisters.allWires,List.append_assoc] using h.physical
  have hn (wire : Wire) (hw : wire ∈ r.lengthRPrime ++ r.aux) : wire ∉ r.sign :: r.work1 := by
    intro hm
    have hm' : wire ∈ pre := by
      simp only [List.mem_cons] at hm
      simp only [pre,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
      aesop
    exact (List.nodup_append.mp hp).2.2 wire hm' wire hw rfl
  have hclean : Clean r.aux final := by
    intro wire hw
    change run (blockBForward r n (certifiedActiveWindows n index).remainder) state wire = false
    rw [hf wire (hn wire (List.mem_append_right _ hw))]
    exact hc wire hw
  have hagree : ∀ wire ∈ r.lengthRPrime, final wire = state wire := by
    intro wire hw
    exact hf wire (hn wire (List.mem_append_left _ hw))
  have hand : wireAnd r.lengthRPrime final = wireAnd r.lengthRPrime state := by
    generalize r.lengthRPrime = wires at hagree ⊢
    induction wires with
    | nil => rfl
    | cons w ws ih =>
      simp only [wireAnd]
      rw [hagree w (by simp),ih (fun v hv => hagree v (by simp [hv]))]
  rw [Classical.run_append]
  exact blockCForward_nonterminal r n index final h hclean (hand.trans hrp)

private theorem remainder_field_frame (r : IndexedStepRegisters) (n index T Q shift : Nat)
    (mode : RippleMode) (signUpdate : Bool) (state : BasisState)
    (h : IndexedStepLayout r n index)
    (hready : IntervalReady (r.remainder (certifiedActiveWindows n index).remainder) state)
    (ht : boolWordToNat (wireValues r.lengthT state) = truthMinusOneValue r.lengthQ.length T)
    (hq : boolWordToNat (wireValues r.lengthQ state) = truthMinusOneValue r.lengthQ.length Q)
    (hs : boolWordToNat (wireValues r.lengthS state) = truthMinusOneValue r.lengthS.length shift)
    (hleftLow : (certifiedActiveWindows n index).remainder.start ≤ T+Q+2) (hleftHigh : T+Q+2-(certifiedActiveWindows n index).remainder.start < 2^r.lengthQ.length)
    (hrightLow : shift+(certifiedActiveWindows n index).remainder.start ≤ n+3) (hrightHigh : n+3-shift-(certifiedActiveWindows n index).remainder.start < 2^r.lengthS.length)
    (hrange : n+3-shift-(certifiedActiveWindows n index).remainder.start ≤ intervalTopRelative (certifiedActiveWindows n index).remainder.start (certifiedActiveWindows n index).remainder.stop)
    (horder : T+Q+2-(certifiedActiveWindows n index).remainder.start ≤ n+3-shift-(certifiedActiveWindows n index).remainder.start) :
    let w := (certifiedActiveWindows n index).remainder
    let final := run (intervalAddSubUnitary (r.remainder w) n w.start w.stop mode signUpdate .work1) state
    (wireValues r.work1 final).take (T+Q+1) = (wireValues r.work1 state).take (T+Q+1) ∧
    (wireValues r.work1 final).drop (n+3-shift) = (wireValues r.work1 state).drop (n+3-shift) := by
  let w := (certifiedActiveWindows n index).remainder
  change w.start ≤ T+Q+2 at hleftLow
  change shift+w.start ≤ n+3 at hrightLow
  change T+Q+2-w.start ≤ n+3-shift-w.start at horder
  have hb := run_remainderInterval_logicalSlices r n index T Q shift mode signUpdate state h hready
    ht hq hs hleftLow hleftHigh hrightLow hrightHigh hrange horder
  have hw : 1 ≤ w.start := by simp only [w,certifiedActiveWindows,certifiedRemainderWindow]; omega
  have hspan : T+Q+1 ≤ n+3-shift := by omega
  have hlen : (wireValues r.work1 state).length = n+3 := by simp only [wireValues,List.length_map,h.work1_length]
  have hwidth : n+3-shift-(T+Q+2)+1 = n+3-shift-(T+Q+1) := by omega
  dsimp only at hb ⊢
  rw [hb.1]
  have hp : ((wireValues r.work1 state).take (T+Q+1)).length = T+Q+1 := by simp only [List.length_take,hlen]; omega
  have hl : (uniformRippleExpectedWords mode (state r.control)
      (((wireValues r.work1 state).drop (T+Q+1)).take (n+3-shift-(T+Q+2)+1))
      (((wireValues r.work2 state).drop (T+Q+1)).take (n+3-shift-(T+Q+2)+1)) false).1.length = n+3-shift-(T+Q+1) := by
    rw [uniformRippleExpectedWords_length,List.length_take,List.length_drop,hlen,hwidth]
    omega
  have general (pre mid post : List Bool) :
      ((pre ++ mid) ++ post).take pre.length = pre ∧
      ((pre ++ mid) ++ post).drop (pre.length+mid.length) = post := by
    simp [List.append_assoc,List.drop_append]
  have hg := general ((wireValues r.work1 state).take (T+Q+1))
    (uniformRippleExpectedWords mode (state r.control)
      (((wireValues r.work1 state).drop (T+Q+1)).take (n+3-shift-(T+Q+2)+1))
      (((wireValues r.work2 state).drop (T+Q+1)).take (n+3-shift-(T+Q+2)+1)) false).1
    ((wireValues r.work1 state).drop (n+3-shift))
  simpa only [hp,hl,Nat.add_sub_of_le hspan] using hg

/-- Block B1 preserves both portions of work1 outside the logical remainder field. -/
theorem blockB1Forward_fieldFrame (r : IndexedStepRegisters) (n index ellT ellQ shift : Nat)
    (state : BasisState) (h : IndexedStepLayout r n index) (hc : Clean r.aux state)
    (ht : boolWordToNat (wireValues r.lengthT state) = truthMinusOneValue r.lengthQ.length ellT)
    (hq : boolWordToNat (wireValues r.lengthQ state) = truthMinusOneValue r.lengthQ.length ellQ)
    (hs : boolWordToNat (wireValues r.lengthS state) = truthMinusOneValue r.lengthS.length shift)
    (hleftLow : (certifiedActiveWindows n index).remainder.start ≤ ellT+ellQ+2)
    (hleftHigh : ellT+ellQ+2-(certifiedActiveWindows n index).remainder.start < 2^r.lengthQ.length)
    (hrightLow : shift+(certifiedActiveWindows n index).remainder.start ≤ n+3)
    (hrightHigh : n+3-shift-(certifiedActiveWindows n index).remainder.start < 2^r.lengthS.length)
    (horder : ellT+ellQ+2-(certifiedActiveWindows n index).remainder.start ≤
      n+3-shift-(certifiedActiveWindows n index).remainder.start) :
    let final := run (blockB1Forward r n (certifiedActiveWindows n index).remainder) state
    (wireValues r.work1 final).take (ellT+ellQ+1) = (wireValues r.work1 state).take (ellT+ellQ+1) ∧
    (wireValues r.work1 final).drop (n+3-shift) = (wireValues r.work1 state).drop (n+3-shift) := by
  let w := (certifiedActiveWindows n index).remainder
  let enabled := state[r.control ↦ (rControlNonterminalPredicate [r.phase1] 0 r.lengthRPrime r.terminal state)]
  let changed := run (intervalAddSubUnitary (r.remainder w) n w.start w.stop .sub true .work1) enabled
  have hf := run_blockB1Forward_interval r n index state h hc
  have hdata (ws : List Wire) (hm : ∀ wire ∈ ws, wire ∈ dataWires r) :
      wireValues ws enabled = wireValues ws state := data_words_update r n index h ws hm state _
  have hT := hdata r.lengthT (by intro wire hw; simp [dataWires,hw])
  have hQ := hdata r.lengthQ (by intro wire hw; simp [dataWires,hw])
  have hS := hdata r.lengthS (by intro wire hw; simp [dataWires,hw])
  have hW1 := hdata r.work1 (by intro wire hw; simp [dataWires,hw])
  have hout := data_words_update r n index h r.work1 (by intro wire hw; simp [dataWires,hw]) changed false
  have hrange : n+3-shift-w.start ≤ intervalTopRelative w.start w.stop := by
    simp only [intervalTopRelative,intervalLaneCount,w,certifiedActiveWindows,certifiedRemainderWindow]
    omega
  have hb := remainder_field_frame r n index ellT ellQ shift .sub true enabled h hf.2.1
    (by simpa only [hT] using ht) (by simpa only [hQ] using hq) (by simpa only [hS] using hs)
    hleftLow hleftHigh hrightLow hrightHigh hrange horder
  dsimp only at hb ⊢
  rw [hf.1,hout]
  simpa only [hW1] using hb

/-- Block B3 preserves both portions of work1 outside the logical remainder field. -/
theorem blockB3Forward_fieldFrame (r : IndexedStepRegisters) (n index ellT ellQ shift : Nat)
    (state : BasisState) (h : IndexedStepLayout r n index) (hc : Clean r.aux state)
    (ht : boolWordToNat (wireValues r.lengthT state) = truthMinusOneValue r.lengthQ.length ellT)
    (hq : boolWordToNat (wireValues r.lengthQ state) = truthMinusOneValue r.lengthQ.length ellQ)
    (hs : boolWordToNat (wireValues r.lengthS state) = truthMinusOneValue r.lengthS.length shift)
    (hleftLow : (certifiedActiveWindows n index).remainder.start ≤ ellT+ellQ+2)
    (hleftHigh : ellT+ellQ+2-(certifiedActiveWindows n index).remainder.start < 2^r.lengthQ.length)
    (hrightLow : shift+(certifiedActiveWindows n index).remainder.start ≤ n+3)
    (hrightHigh : n+3-shift-(certifiedActiveWindows n index).remainder.start < 2^r.lengthS.length)
    (horder : ellT+ellQ+2-(certifiedActiveWindows n index).remainder.start ≤
      n+3-shift-(certifiedActiveWindows n index).remainder.start) :
    let final := run (blockB3Forward r n (certifiedActiveWindows n index).remainder) state
    (wireValues r.work1 final).take (ellT+ellQ+1) = (wireValues r.work1 state).take (ellT+ellQ+1) ∧
    (wireValues r.work1 final).drop (n+3-shift) = (wireValues r.work1 state).drop (n+3-shift) := by
  let w := (certifiedActiveWindows n index).remainder
  let enabled := state[r.control ↦ (!state r.phase1 && !(state r.phase2 && state r.sign) && !wireAnd r.lengthRPrime state)]
  let changed := run (intervalAddSubUnitary (r.remainder w) n w.start w.stop .add false .work1) enabled
  have hf := run_blockB3Forward_interval r n index state h hc
  have hdata (ws : List Wire) (hm : ∀ wire ∈ ws, wire ∈ dataWires r) :
      wireValues ws enabled = wireValues ws state := data_words_update r n index h ws hm state _
  have hT := hdata r.lengthT (by intro wire hw; simp [dataWires,hw])
  have hQ := hdata r.lengthQ (by intro wire hw; simp [dataWires,hw])
  have hS := hdata r.lengthS (by intro wire hw; simp [dataWires,hw])
  have hW1 := hdata r.work1 (by intro wire hw; simp [dataWires,hw])
  have hout := data_words_update r n index h r.work1 (by intro wire hw; simp [dataWires,hw]) changed false
  have hrange : n+3-shift-w.start ≤ intervalTopRelative w.start w.stop := by
    simp only [intervalTopRelative,intervalLaneCount,w,certifiedActiveWindows,certifiedRemainderWindow]
    omega
  have hb := remainder_field_frame r n index ellT ellQ shift .add false enabled h hf.2.1
    (by simpa only [hT] using ht) (by simpa only [hQ] using hq) (by simpa only [hS] using hs)
    hleftLow hleftHigh hrightLow hrightHigh hrange horder
  dsimp only at hb ⊢
  rw [hf.1,hout]
  simpa only [hW1] using hb

end ShorECDLP.Paper2607_13816
