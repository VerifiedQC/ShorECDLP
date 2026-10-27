import ShorECDLP.Submission.«2607_13816».Challenge.OuterTrace
import ShorECDLP.Submission.«2607_13816».Challenge.CertificateAssembly

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge

/-- Hadamards prepare the reused address bank before each window call. -/
def prepareOuterBank {n s e : Nat} (wires : List Wire) (next : Straight n s e) : Straight n s e :=
  wires.foldr (fun w p => .gate (.literal (.H w)) p) next

theorem prepareOuterBank_wellFormed {n s e : Nat} (wires : List Wire) (next : Straight n s e)
    (h : next.WellFormed) : (prepareOuterBank wires next).WellFormed := by
  induction wires with
  | nil => exact h
  | cons w ws ih => exact ⟨trivial, ih⟩

/-- A fixed window body. Its count is syntactic, independent of coordinates and
outcomes; compilation is performed before the protected entry is submitted. -/
structure OuterWindow (n : Nat) where
  count : Nat
  program : (start : Nat) → Straight n start (start + count)

def axisCount {n : Nat} : List (OuterWindow n) → Nat
  | [] => 0
  | w :: ws => w.count + 16 + axisCount ws

def bankPrior {start : Nat} (count : Nat) (prior : List (Fin start)) :
    List (Fin (start + count)) := prior.map (fun i => ⟨i.val, by omega⟩)

/-- Newest Fourier bits first, followed by the older banks on this axis. -/
def nextBankPrior {start : Nat} (count : Nat) (prior : List (Fin start)) :
    List (Fin (start + count + 16)) :=
  (List.ofFn (fun i : Fin 16 => (⟨start + count + i.val, by omega⟩ : Fin (start+count+16)))).reverse ++
    prior.map (fun i => ⟨i.val, by omega⟩)

def outerAxis {n : Nat} (wires : Vector Wire 16) :
    (ws : List (OuterWindow n)) → (start : Nat) → List (Fin start) →
      Straight n start (start + axisCount ws)
  | [], _, _ => .done
  | w :: ws, start, prior =>
    let fourier : Straight n (start+w.count) (start+w.count+16) :=
      castFinish (by simp) (fourierProgram n .inverse wires.toList (start+w.count) (bankPrior w.count prior))
    castFinish (by simp only [axisCount]; omega)
      ((prepareOuterBank wires.toList.reverse (w.program start)).append (fourier.append
        (outerAxis wires ws (start+w.count+16) (nextBankPrior w.count prior))))

/-- Absolute output positions, in chronological order. -/
def axisPositions {n : Nat} : List (OuterWindow n) → Nat → List Nat
  | [], _ => []
  | w :: ws, start => List.range' (start+w.count) 16 ++ axisPositions ws (start+w.count+16)

theorem axisPositions_length {n : Nat} (ws : List (OuterWindow n)) (start : Nat) :
    (axisPositions ws start).length = ws.length * 16 := by
  induction ws generalizing start with
  | nil => simp [axisPositions]
  | cons w ws ih => simp [axisPositions, ih, Nat.add_mul]; omega

theorem axisPositions_bounds {n : Nat} (ws : List (OuterWindow n)) (start i : Nat)
    (hi : i ∈ axisPositions ws start) : start ≤ i ∧ i < start + axisCount ws := by
  induction ws generalizing start with
  | nil => simp [axisPositions] at hi
  | cons w ws ih =>
    rcases List.mem_append.mp hi with hi | hi
    · have h := List.mem_range'.mp hi
      simp only [axisCount]; omega
    · have h := ih _ hi
      simp only [axisCount]; omega

/-- Each bank's extracted word is an actual Fourier branch, evaluated with the
actual history at that bank. This records semantic evidence, not just bounds. -/
def FourierRecord {n : Nat} (wires : Vector Wire 16) (read : ConstantBit n → Bool)
    (whole : List Bool) (i : Nat) : Prop :=
  ∃ (bankStart : Nat) (prior : List (Fin bankStart)) (h : Fin bankStart → Bool)
      (f : InstrumentBranch) (bit : Fin 16),
      f ∈ ((fourierProgram n .inverse wires.toList bankStart prior).instantiate read h).run ∧
      i = bankStart + bit.val ∧ whole[i]? = f.history[bit.val]? ∧
      List.ofFn h = whole.take bankStart

def AxisRecords {n : Nat} (wires : Vector Wire 16) (read : ConstantBit n → Bool)
    (before : List Bool) (ws : List (OuterWindow n)) (start : Nat) (out : List Bool) : Prop :=
  ∀ i ∈ axisPositions ws start, FourierRecord wires read (before ++ out) i

theorem outerAxis_records {n : Nat} (wires : Vector Wire 16) (ws : List (OuterWindow n))
    (start : Nat) (prior : List (Fin start)) (read : ConstantBit n → Bool)
    (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((outerAxis wires ws start prior).instantiate read history).run) :
    AxisRecords wires read (List.ofFn history) ws start b.history := by
  induction ws generalizing start b with
  | nil => intro i hi; simp [axisPositions] at hi
  | cons w ws ih =>
    simp only [outerAxis, castFinish_instantiate] at hb
    obtain ⟨h₁, a, rest, ha, hr, he₁, rfl⟩ := straight_append_branch _ _ read history b hb
    obtain ⟨h₂, f, c, hf, hc, he₂, rfl⟩ := straight_append_branch _ _ read h₁ rest hr
    simp only [castFinish_instantiate] at hf
    have hfull : List.ofFn history ++ (a.seq (f.seq c)).history =
        List.ofFn h₁ ++ f.history ++ c.history := by
      simp only [InstrumentBranch.seq, he₁, List.append_assoc]
    have htail : List.ofFn h₂ ++ c.history =
        List.ofFn history ++ (a.seq (f.seq c)).history := by
      rw [he₂, ← hfull]
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · have hi' := List.mem_range'.mp hi
      let bit : Fin 16 := ⟨i - (start+w.count), by omega⟩
      have hbit : i = start+w.count+bit.val := by dsimp [bit]; omega
      refine ⟨start+w.count, bankPrior w.count prior, h₁, f, bit, hf, hbit, ?_, ?_⟩
      · rw [hfull, hbit]
        exact fourierProgram_record_at n .inverse wires.toList _ _ read h₁ f hf
          (List.ofFn h₁) c.history (by simp) (Fin.cast (by simp) bit)
      · rw [hfull, List.append_assoc]
        have hlen : (List.ofFn h₁).length = start+w.count := by simp
        simpa only [hlen] using (show (List.ofFn h₁ ++ (f.history ++ c.history)).take (List.ofFn h₁).length = List.ofFn h₁ from List.take_left).symm
    · have ht := ih _ _ h₂ c hc i hi
      simpa only [htail] using ht

theorem FourierRecord.suffix {n : Nat} {wires : Vector Wire 16} {read : ConstantBit n → Bool}
    {whole : List Bool} {i : Nat} (h : FourierRecord wires read whole i)
    (hi : i < whole.length) (suffix : List Bool) : FourierRecord wires read (whole ++ suffix) i := by
  obtain ⟨s, prior, history, f, bit, hf, he, hv, hh⟩ := h
  refine ⟨s, prior, history, f, bit, hf, he, ?_, ?_⟩
  · rwa [List.getElem?_append_left hi]
  · rw [List.take_append_of_le_length (by omega : s ≤ whole.length)]
    exact hh

structure OuterPlan (n : Nat) where
  wires : Vector Wire 16
  left : Vector (OuterWindow n) 16
  right : Vector (OuterWindow n) 13
  reset : List Wire

def OuterPlan.stride {n : Nat} (p : OuterPlan n) : Nat :=
  axisCount p.left.toList + axisCount p.right.toList + p.reset.length

/-- The control wire is toggled around both axes, as in streamRawTrial. Reset
wires remain a supplied fixed list: completeness of that list is a producer obligation. -/
def OuterPlan.round {n : Nat} (p : OuterPlan n) (start : Nat) :
    Straight n start (start+p.stride) :=
  castFinish (by simp only [OuterPlan.stride]; omega)
    (.gate (.literal (.X 836)) ((outerAxis p.wires p.left.toList start List.nil).append
      ((outerAxis p.wires p.right.toList (start+axisCount p.left.toList) List.nil).append
        (.gate (.literal (.X 836)) (resetProgram n
          (start+axisCount p.left.toList+axisCount p.right.toList) p.reset)))))

def OuterPlan.repeat {n : Nat} (p : OuterPlan n) :
    (trials start : Nat) → Straight n start (start+trials*p.stride)
  | 0, start => castFinish (by simp) (.done : Straight n start start)
  | k+1, start => castFinish (by simp [Nat.add_mul, Nat.add_assoc, Nat.add_comm])
      ((p.round start).append (p.repeat k (start+p.stride)))

def OuterPlan.entry (coefficients : List PointCoeff) (p : OuterPlan coefficients.length) : StraightEntry :=
  ⟨coefficients, 56*p.stride, castFinish (by omega) (p.repeat 56 0)⟩

def OuterPlan.positions {n : Nat} (p : OuterPlan n) (r : Fin 56) : TrialPositions legacyDecoderParams where
  left := ⟨(axisPositions p.left.toList (r.val*p.stride)).toArray, by simp [axisPositions_length, legacyDecoderParams]⟩
  right := ⟨(axisPositions p.right.toList (r.val*p.stride+axisCount p.left.toList)).toArray,
    by simp [axisPositions_length, legacyDecoderParams]⟩

def OuterPlan.layout {n : Nat} (p : OuterPlan n) : DecodeLayout :=
  ⟨.wrappedShift, legacyDecoderParams, List.ofFn p.positions, by simp⟩

theorem OuterPlan.round_records {n : Nat} (p : OuterPlan n) (start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((p.round start).instantiate read history).run) :
    ∀ i ∈ axisPositions p.left.toList start ++
      axisPositions p.right.toList (start+axisCount p.left.toList),
      FourierRecord p.wires read (List.ofFn history ++ b.history) i := by
  simp only [OuterPlan.round, castFinish_instantiate, Straight.instantiate, AdaptiveCircuit.run] at hb
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hb
  obtain ⟨h₁, a, rest, ha, hr, he₁, rfl⟩ := straight_append_branch _ _ read history d hd
  obtain ⟨h₂, f, c, hf, hc, he₂, rfl⟩ := straight_append_branch _ _ read h₁ rest hr
  change ∀ i ∈ _, FourierRecord p.wires read (List.ofFn history ++ (a.seq (f.seq c)).history) i
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · have h := outerAxis_records p.wires p.left.toList start List.nil read history a ha i hi
    have hl := straight_history_length _ read history a ha
    have bound := axisPositions_bounds p.left.toList start i hi
    have hh : i < (List.ofFn history ++ a.history).length := by simp only [List.length_append, List.length_ofFn]; omega
    simpa only [InstrumentBranch.seq, List.append_assoc] using h.suffix hh (f.history ++ c.history)
  · have h := outerAxis_records p.wires p.right.toList _ List.nil read h₁ f hf i hi
    have hl := straight_history_length _ read h₁ f hf
    have bound := axisPositions_bounds p.right.toList (start+axisCount p.left.toList) i hi
    have hh : i < (List.ofFn h₁ ++ f.history).length := by simp only [List.length_append, List.length_ofFn]; omega
    simpa only [he₁, InstrumentBranch.seq, List.append_assoc] using h.suffix hh c.history

/-- Repetition uses actual round output histories, so resets and earlier rounds
contribute to the absolute cursor but never enter Fourier words. -/
theorem OuterPlan.repeat_records {n : Nat} (p : OuterPlan n) (count start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((p.repeat count start).instantiate read history).run)
    (r : Nat) (hr : r < count) :
    ∀ i ∈ axisPositions p.left.toList (start+r*p.stride) ++
      axisPositions p.right.toList (start+r*p.stride+axisCount p.left.toList),
      FourierRecord p.wires read (List.ofFn history ++ b.history) i := by
  induction count generalizing start b r with
  | zero => omega
  | succ count ih =>
    simp only [OuterPlan.repeat, castFinish_instantiate] at hb
    obtain ⟨h₁, a, c, ha, hc, he, rfl⟩ := straight_append_branch _ _ read history b hb
    cases r with
    | zero =>
      simp only [Nat.zero_mul, Nat.add_zero]
      intro i hi
      have h := p.round_records start read history a ha i hi
      have hl := straight_history_length _ read history a ha
      have bound : i < start+p.stride := by
        rcases List.mem_append.mp hi with hi | hi
        · have h := axisPositions_bounds p.left.toList start i hi
          simp only [OuterPlan.stride]; omega
        · have h := axisPositions_bounds p.right.toList (start+axisCount p.left.toList) i hi
          simp only [OuterPlan.stride]; omega
      have hh : i < (List.ofFn history ++ a.history).length := by simp only [List.length_append, List.length_ofFn]; omega
      simpa only [InstrumentBranch.seq, List.append_assoc] using h.suffix hh c.history
    | succ r =>
      have h := ih (start+p.stride) h₁ c hc r (by omega)
      simpa only [he, InstrumentBranch.seq, List.append_assoc, Nat.succ_mul,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

theorem OuterPlan.entry_records (coefficients : List PointCoeff) (p : OuterPlan coefficients.length)
    (Q : Secp256k1.Point) (b : InstrumentBranch) (hb : b ∈ ((p.entry coefficients).instantiate Q).run)
    (r : Fin 56) :
    ∀ i ∈ (p.positions r).left.toList ++ (p.positions r).right.toList,
      FourierRecord p.wires (readConstant coefficients.get Q) b.history i := by
  simp only [OuterPlan.entry, StraightEntry.instantiate, castFinish_instantiate] at hb
  have h := p.repeat_records 56 0 (readConstant coefficients.get Q) Fin.elim0 b hb r.val r.isLt
  simpa only [OuterPlan.positions, Vector.toList, List.toList_toArray, List.ofFn_zero,
    List.nil_append, Nat.zero_add] using h

theorem straight_append_wellFormed {n s m e : Nat} (p : Straight n s m) (q : Straight n m e)
    (hp : p.WellFormed) (hq : q.WellFormed) : (p.append q).WellFormed := by
  induction p with
  | done => exact hq
  | gate g p ih => exact ⟨hp.1, ih q hp.2 hq⟩
  | recordGate i v g p ih => exact ⟨hp.1, ih q hp.2 hq⟩
  | measure w p ih => exact ih q hp hq

theorem resetProgram_wellFormed (n start : Nat) (ws : List Wire) :
    (resetProgram n start ws).WellFormed := by
  induction ws generalizing start with
  | nil => trivial
  | cons w ws ih => simpa only [resetProgram, castFinish_wellFormed, Straight.WellFormed] using ih (start+1)

theorem outerAxis_wellFormed {n : Nat} (wires : Vector Wire 16) (ws : List (OuterWindow n))
    (hw : ∀ w ∈ ws, ∀ start, (w.program start).WellFormed)
    (start : Nat) (prior : List (Fin start)) : (outerAxis wires ws start prior).WellFormed := by
  induction ws generalizing start with
  | nil => trivial
  | cons w ws ih =>
    simp only [outerAxis, castFinish_wellFormed]
    apply straight_append_wellFormed _ _ (prepareOuterBank_wellFormed _ _ (hw w (by simp) start))
    apply straight_append_wellFormed
    · simpa only [castFinish_wellFormed] using fourierProgram_wellFormed n .inverse wires.toList _ _
    · exact ih (fun v hv => hw v (List.mem_cons_of_mem w hv)) _ _

def OuterPlan.WindowsWellFormed {n : Nat} (p : OuterPlan n) : Prop :=
  ∀ w ∈ p.left.toList ++ p.right.toList, ∀ start, (w.program start).WellFormed

theorem OuterPlan.round_wellFormed {n : Nat} (p : OuterPlan n) (hp : p.WindowsWellFormed) (start : Nat) :
    (p.round start).WellFormed := by
  simp only [OuterPlan.round, castFinish_wellFormed, Straight.WellFormed]
  refine ⟨trivial, straight_append_wellFormed _ _ ?_ (straight_append_wellFormed _ _ ?_ ?_)⟩
  · exact outerAxis_wellFormed _ _ (fun w hw => hp w (List.mem_append_left _ hw)) _ _
  · exact outerAxis_wellFormed _ _ (fun w hw => hp w (List.mem_append_right _ hw)) _ _
  · exact ⟨trivial, resetProgram_wellFormed _ _ _⟩

theorem OuterPlan.repeat_wellFormed {n : Nat} (p : OuterPlan n) (hp : p.WindowsWellFormed) (count start : Nat) :
    (p.repeat count start).WellFormed := by
  induction count generalizing start with
  | zero => simp only [OuterPlan.repeat, castFinish_wellFormed, Straight.WellFormed]
  | succ k ih =>
    simp only [OuterPlan.repeat, castFinish_wellFormed]
    exact straight_append_wellFormed _ _ (p.round_wellFormed hp _) (ih _)

theorem OuterPlan.entry_history_length (coefficients : List PointCoeff) (p : OuterPlan coefficients.length)
    (Q : Secp256k1.Point) (b : InstrumentBranch) (hb : b ∈ ((p.entry coefficients).instantiate Q).run) :
    b.history.length = 56*p.stride := by
  have h := straight_history_length (p.entry coefficients).program (readConstant coefficients.get Q) Fin.elim0 b hb
  simpa only [OuterPlan.entry, Nat.sub_zero] using h

theorem FourierRecord.present {n : Nat} {wires : Vector Wire 16} {read : ConstantBit n → Bool}
    {whole : List Bool} {i : Nat} (h : FourierRecord wires read whole i) : ∃ bit, whole[i]? = some bit := by
  obtain ⟨s, prior, history, f, bit, hf, _, hv, _⟩ := h
  have hl := (fourierProgram_branch n .inverse wires.toList s prior read history f hf).1
  have hi : bit.val < f.history.length := by simpa only [hl, Vector.length_toList] using bit.isLt
  exact ⟨f.history[bit.val], hv.trans (List.getElem?_eq_getElem hi)⟩

theorem readWord_present (history : List Bool) (positions : List Nat)
    (hp : ∀ i ∈ positions, ∃ bit, history[i]? = some bit) : ∃ word, readWord history positions = some word := by
  induction positions with
  | nil => exact ⟨0, rfl⟩
  | cons i is ih =>
    obtain ⟨b, hb⟩ := hp i (by simp)
    obtain ⟨w, hw⟩ := ih (fun j hj => hp j (List.mem_cons_of_mem i hj))
    exact ⟨(if b then 1 else 0) + 2*w, by simp [readWord, hb, hw]⟩

/-- Both protected decoder reads succeed on each actual round's Fourier data. -/
theorem OuterPlan.entry_reads (coefficients : List PointCoeff) (p : OuterPlan coefficients.length)
    (Q : Secp256k1.Point) (b : InstrumentBranch) (hb : b ∈ ((p.entry coefficients).instantiate Q).run)
    (r : Fin 56) :
    (∃ left, readWord b.history (p.positions r).left.toList = some left) ∧
    (∃ right, readWord b.history (p.positions r).right.toList = some right) := by
  have h := p.entry_records coefficients Q b hb r
  exact ⟨readWord_present _ _ (fun i hi => (h i (List.mem_append_left _ hi)).present),
    readWord_present _ _ (fun i hi => (h i (List.mem_append_right _ hi)).present)⟩

/-- Final semantic success and resource inequalities are still producer proofs.
The outer construction supplies the fixed precision, decoder and physical composition. -/
theorem OuterPlan.assembly (coefficients : List PointCoeff) (p : OuterPlan coefficients.length)
    (hp : p.WindowsWellFormed) (bounds : Bounds)
    (hr : ∀ Q : Secp256k1.Point,
      (resources ((p.entry coefficients).instantiate Q)).qubits ≤ bounds.qubits ∧
      (resources ((p.entry coefficients).instantiate Q)).tModel ≤ bounds.tModel ∧
      (resources ((p.entry coefficients).instantiate Q)).measurements ≤ bounds.measurements)
    (hs : ∀ (Q : Secp256k1.Point) (d : Nat), Q ≠ 0 → Q = d • Secp256k1.G →
      (99 : ℝ)/100 ≤ Instrument.bornMass
        (((p.entry coefficients).instantiate Q).run.filter
          (fun b => (verifiedCandidate p.layout Q b.history).isSome)) (ket zeroBasisState)) :
    StreamingAssembly p.layout (p.entry coefficients) bounds where
  kind := rfl
  precision := rfl
  wellFormed := by simpa only [OuterPlan.entry, castFinish_wellFormed] using p.repeat_wellFormed hp 56 0
  resources := hr
  success := hs

theorem OuterPlan.layout_trial {n : Nat} (p : OuterPlan n) (r : Fin 56) :
    p.layout.trials[r.val]? = some (p.positions r) := by
  simp only [OuterPlan.layout, List.getElem?_ofFn, dif_pos r.isLt]

theorem OuterPlan.candidate_budget {n : Nat} (p : OuterPlan n) (history : List Bool) :
    (candidates p.layout history).length ≤ budget55 :=
  streaming_candidates_length p.layout rfl rfl history

/-- Canonical reused-bank Fourier order; changing scratch space changes only
producer windows and the explicit reset list, not the 256/208-bit readout shape. -/
def standardOuterPlan {n : Nat} (left : Vector (OuterWindow n) 16)
    (right : Vector (OuterWindow n) 13) (reset : List Wire) : OuterPlan n where
  wires := ⟨(List.range' 855 16).reverse.toArray, by simp⟩
  left := left
  right := right
  reset := reset

end ShorECDLP.Paper2607_13816.ChallengeMigration
