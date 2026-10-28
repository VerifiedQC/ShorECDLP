import ShorECDLP.Submission.«2607_13816».Challenge.TwoAxisProbability
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

/-- The evaluator reads exactly the supplied chronological bits, with its fixed LSB convention. -/
theorem readWord_of_actual_bits (history : List Bool) (positions : List Nat) (bits : List Bool)
    (h : positions.map (fun i => history[i]?) = bits.map some) :
    readWord history positions = some (fourierWordLSB bits) := by
  induction positions generalizing bits with
  | nil =>
    cases bits with
    | nil => rfl
    | cons b bits => simp at h
  | cons i positions ih =>
    cases bits with
    | nil => simp at h
    | cons b bits =>
      have hh : history[i]? = some b ∧
          positions.map (fun j => history[j]?) = bits.map some := by
        simpa only [List.map_cons,List.cons.injEq] using h
      simp only [readWord,hh.1,ih bits hh.2,fourierWordLSB]
      cases b <;> rfl

theorem actual_bits_range (before bits after : List Bool) :
    (List.range' before.length bits.length).map
      (fun i => (before ++ bits ++ after)[i]?) = bits.map some := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.length_map,List.length_range'] at hi
    simp only [List.getElem_map,List.getElem_range']
    rw [List.append_assoc, List.getElem?_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left,Nat.one_mul]
    rw [List.getElem?_append_left hi,List.getElem?_eq_getElem hi]

theorem readWord_actual_range (before bits after : List Bool) :
    readWord (before ++ bits ++ after) (List.range' before.length bits.length) =
      some (fourierWordLSB bits) :=
  readWord_of_actual_bits _ _ _ (actual_bits_range before bits after)


/-- A transcript decomposition records each arithmetic prefix and the next sixteen Fourier bits. -/
inductive AxisTranscript {n : Nat} : List (OuterWindow n) → List Bool → List Bool → Prop
  | nil : AxisTranscript List.nil List.nil List.nil
  | cons (w : OuterWindow n) (ws : List (OuterWindow n)) (a bits rest out : List Bool)
      (ha : a.length = w.count) (hb : bits.length = 16)
      (ht : AxisTranscript ws rest out) :
      AxisTranscript (w :: ws) (a ++ bits ++ rest) (bits ++ out)

theorem AxisTranscript.actual_bits {n : Nat} {ws : List (OuterWindow n)}
    {history bits : List Bool} (h : AxisTranscript ws history bits)
    (before after : List Bool) :
    (axisPositions ws before.length).map (fun i => (before ++ history ++ after)[i]?) =
      bits.map some := by
  induction h generalizing before with
  | nil => rfl
  | cons w ws a bs rest out ha hb ht ih =>
    rw [axisPositions,List.map_append,List.map_append]
    have hhead := actual_bits_range (before ++ a) bs (rest ++ after)
    have htail := ih (before ++ a ++ bs)
    simp only [List.length_append,ha,hb,List.append_assoc] at hhead htail
    simp only [List.append_assoc,Nat.add_assoc]
    rw [hhead,htail]

theorem AxisTranscript.readWord {n : Nat} {ws : List (OuterWindow n)}
    {history bits : List Bool} (h : AxisTranscript ws history bits)
    (before after : List Bool) :
    ShorECDLP.Challenge.readWord (before ++ history ++ after) (axisPositions ws before.length) =
      some (fourierWordLSB bits) :=
  readWord_of_actual_bits _ _ _ (h.actual_bits before after)


/-- Transcript blocks are obtained from the actual straight execution, not supplied as an assumption. -/
theorem outerAxis_transcript {n : Nat} (wires : Vector Wire 16)
    (ws : List (OuterWindow n)) (start : Nat) (prior : List (Fin start))
    (read : ConstantBit n → Bool) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((outerAxis wires ws start prior).instantiate read history).run) :
    ∃ bits, AxisTranscript ws b.history bits := by
  induction ws generalizing start b with
  | nil =>
    simp only [outerAxis,Straight.instantiate,AdaptiveCircuit.run,List.mem_singleton] at hb
    subst b
    exact ⟨[],AxisTranscript.nil⟩
  | cons w ws ih =>
    simp only [outerAxis,castFinish_instantiate] at hb
    obtain ⟨h₁,a,rest,ha,hr,he₁,rfl⟩ := straight_append_branch _ _ read history b hb
    obtain ⟨h₂,f,c,hf,hc,he₂,rfl⟩ := straight_append_branch _ _ read h₁ rest hr
    obtain ⟨bits,hbits⟩ := ih _ _ h₂ c hc
    have hla : a.history.length = w.count := by
      have h := straight_history_length _ read history a ha
      omega
    have hlf : f.history.length = 16 := by
      have h := straight_history_length _ read h₁ f hf
      omega
    refine ⟨f.history ++ bits,?_⟩
    simpa only [InstrumentBranch.seq,List.append_assoc] using
      AxisTranscript.cons w ws a.history f.history c.history bits hla hlf hbits

theorem outerAxis_readWord {n : Nat} (wires : Vector Wire 16)
    (ws : List (OuterWindow n)) (start : Nat) (prior : List (Fin start))
    (read : ConstantBit n → Bool) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((outerAxis wires ws start prior).instantiate read history).run)
    (suffix : List Bool) :
    ∃ bits, AxisTranscript ws b.history bits ∧
      readWord (List.ofFn history ++ b.history ++ suffix) (axisPositions ws start) =
        some (fourierWordLSB bits) := by
  obtain ⟨bits,h⟩ := outerAxis_transcript wires ws start prior read history b hb
  exact ⟨bits,h,by simpa only [List.length_ofFn] using h.readWord (List.ofFn history) suffix⟩


theorem AxisTranscript.bits_length {n : Nat} {ws : List (OuterWindow n)}
    {history bits : List Bool} (h : AxisTranscript ws history bits) :
    bits.length = ws.length * 16 := by
  induction h with
  | nil => rfl
  | cons w ws a bs rest out ha hb ht ih =>
    simp only [List.length_append,List.length_cons,hb,ih,Nat.add_mul]
    omega

theorem OuterPlan.round_actualWords {n : Nat} (p : OuterPlan n) (start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((p.round start).instantiate read history).run) (suffix : List Bool) :
    ∃ left right : List Bool, left.length = 256 ∧ right.length = 208 ∧
      readWord (List.ofFn history ++ b.history ++ suffix)
        (axisPositions p.left.toList start) = some (fourierWordLSB left) ∧
      readWord (List.ofFn history ++ b.history ++ suffix)
        (axisPositions p.right.toList (start + axisCount p.left.toList)) =
          some (fourierWordLSB right) := by
  simp only [OuterPlan.round,castFinish_instantiate,Straight.instantiate,AdaptiveCircuit.run] at hb
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hb
  obtain ⟨h₁,a,rest,ha,hr,he₁,rfl⟩ := straight_append_branch _ _ read history d hd
  obtain ⟨h₂,f,c,hf,hc,he₂,rfl⟩ := straight_append_branch _ _ read h₁ rest hr
  obtain ⟨left,hl,hlread⟩ := outerAxis_readWord p.wires p.left.toList start List.nil
    read history a ha (f.history ++ c.history ++ suffix)
  obtain ⟨right,hr,hrread⟩ := outerAxis_readWord p.wires p.right.toList _ List.nil
    read h₁ f hf (c.history ++ suffix)
  refine ⟨left,right,?_,?_,?_,?_⟩
  · simpa using hl.bits_length
  · simpa using hr.bits_length
  · change readWord (List.ofFn history ++ (a.seq (f.seq c)).history ++ suffix) _ = _
    simpa only [InstrumentBranch.seq,List.append_assoc] using hlread
  · change readWord (List.ofFn history ++ (a.seq (f.seq c)).history ++ suffix) _ = _
    simpa only [he₁,InstrumentBranch.seq,List.append_assoc] using hrread



theorem OuterPlan.repeat_actualWords {n : Nat} (p : OuterPlan n) (count start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((p.repeat count start).instantiate read history).run)
    (r : Nat) (hr : r < count) (suffix : List Bool) :
    ∃ left right : List Bool, left.length = 256 ∧ right.length = 208 ∧
      readWord (List.ofFn history ++ b.history ++ suffix)
        (axisPositions p.left.toList (start + r*p.stride)) = some (fourierWordLSB left) ∧
      readWord (List.ofFn history ++ b.history ++ suffix)
        (axisPositions p.right.toList (start + r*p.stride + axisCount p.left.toList)) =
          some (fourierWordLSB right) := by
  induction count generalizing start b r with
  | zero => omega
  | succ count ih =>
    simp only [OuterPlan.repeat,castFinish_instantiate] at hb
    obtain ⟨h₁,a,c,ha,hc,he,rfl⟩ := straight_append_branch _ _ read history b hb
    cases r with
    | zero =>
      simpa only [Nat.zero_mul,Nat.add_zero,InstrumentBranch.seq,List.append_assoc] using
        p.round_actualWords start read history a ha (c.history ++ suffix)
    | succ r =>
      have h := ih (start+p.stride) h₁ c hc r (by omega)
      simpa only [he,InstrumentBranch.seq,List.append_assoc,Nat.succ_mul,
        Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h

theorem OuterPlan.entry_actualWords (coefficients : List PointCoeff)
    (p : OuterPlan coefficients.length) (Q : Secp256k1.Point)
    (b : InstrumentBranch) (hb : b ∈ ((p.entry coefficients).instantiate Q).run) (r : Fin 56) :
    ∃ left right : List Bool, left.length = 256 ∧ right.length = 208 ∧
      readWord b.history (p.positions r).left.toList = some (fourierWordLSB left) ∧
      readWord b.history (p.positions r).right.toList = some (fourierWordLSB right) := by
  simp only [OuterPlan.entry,StraightEntry.instantiate,castFinish_instantiate] at hb
  have h := p.repeat_actualWords 56 0 (readConstant coefficients.get Q) Fin.elim0 b hb r.val r.isLt List.nil
  simpa only [OuterPlan.positions,Vector.toList,List.toList_toArray,List.ofFn_zero,
    List.nil_append,List.append_nil,Nat.zero_add] using h
end ShorECDLP.Paper2607_13816.ChallengeMigration
