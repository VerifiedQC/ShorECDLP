import ShorECDLP.Submission.«2607_13816».Window.StreamHistory
import ShorECDLP.Submission.«2607_13816».Challenge.Lookup
import ShorECDLP.Submission.«2607_13816».Challenge.Coefficients

namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1

theorem constantBits_ofFn (width value : Nat) :
    constantBits width value = List.ofFn (fun i : Fin width => value.testBit i.val) := by
  induction width generalizing value with
  | zero => rfl
  | succ w ih =>
    have hs : constantBits (w+1) value = value.testBit 0 :: constantBits w (value/2) := by
      unfold constantBits
      simp only [List.replicate_succ, xorConstantBits]
      cases value.testBit 0 <;> simp
    rw [hs, ih, List.ofFn_succ]
    congr 1
    apply congrArg List.ofFn
    funext i
    exact Nat.testBit_div_two value i.val

def pointRefs {n : Nat} (row : Fin n) : List (ConstantBit n) :=
  List.ofFn (fun i : Fin 256 => ⟨row, .x, i⟩) ++
  List.ofFn (fun i : Fin 256 => ⟨row, .y, i⟩) ++ [⟨row, .infinity, ⟨0, by decide⟩⟩]

theorem pointRefs_read {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point) (row : Fin n) :
    (pointRefs row).map (readConstant coeffs Q) =
      pointCoordinateWord (fig14PointEncoding (constantPoint Q (coeffs row))) := by
  simp only [pointRefs, List.map_append, List.map_ofFn, List.map_cons, List.map_nil,
    pointCoordinateWord, constantBits_ofFn]
  have hp (P : Point) : pointCoordinates P = fig14PointEncoding P := by cases P <;> rfl
  have hb (b : Bool) : (if b then 1 else 0 : Nat).testBit 0 = b := by cases b <;> rfl
  simp only [Function.comp_def, readConstant, fieldValue, hp, hb]

theorem filtered_zip_mask {α : Type} (refs : List α) (ws : List Wire) (read : α → Bool) :
    (((refs.zip ws).filter (fun p => read p.1)).map Prod.snd) = tableBitsMask ws (refs.map read) := by
  induction refs generalizing ws with
  | nil => cases ws <;> rfl
  | cons r rs ih =>
    cases ws with
    | nil => rfl
    | cons w ws => cases hr : read r <;> simp [hr, tableBitsMask, ih]

def pointLeaf {n : Nat} (row : Fin n) (q : Wire) : List (TemplateGate n) :=
  lookupLeafGates q ((pointRefs row).zip pointLogicalWires)

theorem pointLeaf_instantiate {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (q : Wire) :
    (pointLeaf row q).flatMap (TemplateGate.instantiate (readConstant coeffs Q)) =
      tableXorGates q (pointTableMask (fun _ => constantPoint Q (coeffs row)) 0) := by
  rw [pointLeaf, lookupLeafGates_instantiate]
  rw [show (fun p : ConstantBit n × Wire => Gate.CX q p.2) =
    (Gate.CX q) ∘ Prod.snd from rfl, ← List.map_map, filtered_zip_mask, pointRefs_read]
  rfl

theorem tableAddressTree_label (bits : List Wire) (base stride label : Nat)
    (hl : label ∈ (tableAddressTree bits base stride).labels) :
    ∃ i < 2^bits.length, label = base + stride*i := by
  induction bits generalizing base stride with
  | nil => simp [tableAddressTree, UnaryActionTree.labels] at hl; subst label; exact ⟨0, by simp, by simp⟩
  | cons b bits ih =>
    simp only [tableAddressTree, UnaryActionTree.labels, List.mem_append] at hl
    rcases hl with hz | ho
    · obtain ⟨i, hi, he⟩ := ih base (2*stride) hz
      refine ⟨2*i, ?_, ?_⟩
      · simp only [List.length_cons, pow_succ]; omega
      · rw [he]; ring
    · obtain ⟨i, hi, he⟩ := ih (base+stride) (2*stride) ho
      refine ⟨2*i+1, ?_, ?_⟩
      · simp only [List.length_cons, pow_succ]; omega
      · rw [he]; ring

theorem unaryAction_leaf_congr (tree : UnaryActionTree) (q : Wire) (anc : List Wire)
    (f g : Nat → Wire → Circuit) (h : ∀ l ∈ tree.labels, ∀ w, f l w = g l w) :
    unaryAction .inc f tree q anc = unaryAction .inc g tree q anc := by
  induction tree generalizing q anc with
  | leaf l => simp [unaryAction, h l (by simp [UnaryActionTree.labels])]
  | node bit zero one ihz iho =>
    have hz : ∀ l ∈ zero.labels, ∀ w, f l w = g l w := by
      intro l hl w; exact h l (by simp [UnaryActionTree.labels, hl]) w
    have ho : ∀ l ∈ one.labels, ∀ w, f l w = g l w := by
      intro l hl w; exact h l (by simp [UnaryActionTree.labels, hl]) w
    cases anc <;> simp [unaryAction, ihz _ _ hz, iho _ _ ho]

def firstCoefficients : List PointCoeff := List.ofFn (fun i : Fin 65536 => firstWindowCoefficients i.val)

theorem firstCoefficients_length : firstCoefficients.length = 65536 := List.length_ofFn

/-- The finite submitted list supplies exactly the coefficients used by the run proof. -/
theorem firstCoefficients_get (i : Fin 65536) :
    firstCoefficients[i.val]'(by rw [firstCoefficients_length]; exact i.isLt) =
      firstWindowCoefficients i.val := by
  simp only [firstCoefficients, List.getElem_ofFn]

def firstLookupOps : List (LookupOp 65536) :=
  unaryLookupOps (fun l q => pointLeaf ⟨l % 65536, Nat.mod_lt _ (by decide)⟩ q)
    (tableAddressTree (List.range' 855 16) 0 1) 836 (List.range' 519 16)

theorem firstLookupOps_circuit (Q : Point) (hQ : order • Q = 0) :
    lookupCircuit (readConstant (fun i : Fin 65536 => firstWindowCoefficients i.val) Q) firstLookupOps =
    physicalPointLookup (firstWindowTable (axisWindowOffset G 16 + axisWindowOffset Q 13)
      ((2^(16*15)) • G)) := by
  rw [firstLookupOps, unaryLookupOps_circuit]
  unfold physicalPointLookup directPointLookup tableLookupProgram tableLookup
  apply unaryAction_leaf_congr
  intro l hl q
  obtain ⟨i, hi, he⟩ := tableAddressTree_label _ 0 1 l hl
  have hlt : l < 65536 := by simpa [he] using hi
  rw [pointLeaf_instantiate]
  simp only [Nat.mod_eq_of_lt hlt, firstWindowCoefficients_point _ Q hQ, pointTableMask]

theorem firstLookupOps_measurements : lookupMeasurements firstLookupOps = 65535 := by
  rw [firstLookupOps, unaryLookupOps_measurements _ _ _ _
    (tableAddressTree_layout _ _ _ _ _ (by decide) (by decide))]
  have h := tableAddressTree_nodes (List.range' 855 16) 0 1
  simp only [List.length_range'] at h
  omega

def firstLookupProgram (start : Nat) : Straight 65536 start (start + 65535) :=
  castFinish (by rw [firstLookupOps_measurements]) (lookupProgram 65536 firstLookupOps start)

theorem firstLookupProgram_run (start : Nat) (Q : Point) (hQ : order • Q = 0)
    (history : Fin start → Bool) :
    ((firstLookupProgram start).instantiate
      (readConstant (fun i : Fin 65536 => firstWindowCoefficients i.val) Q) history).run =
    (physicalPointLookup (firstWindowTable (axisWindowOffset G 16 + axisWindowOffset Q 13)
      ((2^(16*15)) • G))).run := by
  rw [firstLookupProgram, castFinish_instantiate, lookupProgram_run, firstLookupOps_circuit Q hQ]

theorem firstLookupProgram_tCount (start : Nat) (Q : Point) (hQ : order • Q = 0)
    (history : Fin start → Bool) :
    ((firstLookupProgram start).instantiate
      (readConstant (fun i : Fin 65536 => firstWindowCoefficients i.val) Q) history).tCount = 458745 := by
  rw [firstLookupProgram, castFinish_instantiate, lookupProgram_tCount, firstLookupOps_circuit Q hQ]
  exact (physicalPointLookup_resources _).1

theorem firstLookupProgram_records (start : Nat) (read : ConstantBit 65536 → Bool)
    (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((firstLookupProgram start).instantiate read history).run) :
    b.history.length = 65535 := by
  have h := straight_history_length (firstLookupProgram start) read history b hb
  simpa using h

attribute [local irreducible] firstLookupProgram firstLookupOps physicalPointLookup firstWindowCoefficients
  Straight.append Straight.instantiate AdaptiveCircuit.run AdaptiveCircuit.seq fourierProgram semiclassicalFourier

def firstWindowProgram (start : Nat) : Straight 65536 start (start+65551) :=
  castFinish (by simp [streamAddress])
    ((literalProgram (streamAddress.map Gate.H)).append
      ((firstLookupProgram start).append
        (fourierProgram 65536 .inverse streamAddress.reverse (start+65535) List.nil)))

theorem firstWindowProgram_run (start : Nat) (Q : Point) (hQ : order • Q = 0)
    (history : Fin start → Bool) :
    ((firstWindowProgram start).instantiate
      (readConstant (fun i : Fin 65536 => firstWindowCoefficients i.val) Q) history).run =
    (measuredStreamBlock (physicalPointLookup
      (firstWindowTable (axisWindowOffset G 16 + axisWindowOffset Q 13) ((2^(16*15)) • G))) List.nil).run := by
  let read := readConstant (fun i : Fin 65536 => firstWindowCoefficients i.val) Q
  let call := physicalPointLookup
    (firstWindowTable (axisWindowOffset G 16 + axisWindowOffset Q 13) ((2^(16*15)) • G))
  have inner (h : Fin start → Bool) :
      (((firstLookupProgram start).append
        (fourierProgram 65536 .inverse streamAddress.reverse (start+65535) List.nil)).instantiate read h).run =
      (call.seq (semiclassicalFourier .inverse streamAddress.reverse List.nil)).run := by
    have hf (h : Fin (start+65535) → Bool) :
        ((fourierProgram 65536 .inverse streamAddress.reverse (start+65535) List.nil).instantiate read h).run =
        (semiclassicalFourier .inverse streamAddress.reverse List.nil).run :=
      fourierProgram_run 65536 .inverse streamAddress.reverse (start+65535) List.nil read h
    rw [append_run_fixed _ _ read h (semiclassicalFourier .inverse streamAddress.reverse List.nil) hf]
    rw [AdaptiveCircuit.run_seq, firstLookupProgram_run start Q hQ, ← AdaptiveCircuit.run_seq]
  simp only [firstWindowProgram, castFinish_instantiate]
  rw [append_run_fixed _ _ _ _ _ inner, AdaptiveCircuit.run_seq, literalProgram_run,
    ← AdaptiveCircuit.run_seq]
  rw [measuredStreamBlock, adaptive_seq_assoc]

theorem firstWindowProgram_records (start : Nat) (read : ConstantBit 65536 → Bool)
    (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((firstWindowProgram start).instantiate read history).run) :
    b.history.length = 65551 := by
  have h := straight_history_length (firstWindowProgram start) read history b hb
  simpa using h

/-- The fixed slice is the tagged Fourier outcome of this actual compiled window. -/
theorem firstWindowProgram_fourier (start : Nat) (Q : Point) (hQ : order • Q = 0)
    (history : Fin start → Bool) (b : InstrumentBranch)
    (hb : b ∈ ((firstWindowProgram start).instantiate
      (readConstant (fun i : Fin 65536 => firstWindowCoefficients i.val) Q) history).run) :
    (b.history.drop 65535, b) ∈ streamBlockOutcomes (physicalPointLookup
      (firstWindowTable (axisWindowOffset G 16 + axisWindowOffset Q 13) ((2^(16*15)) • G))) List.nil := by
  have hlen := firstWindowProgram_records start _ history b hb
  rw [firstWindowProgram_run start Q hQ, ← streamBlockOutcomes_run] at hb
  obtain ⟨tagged, ht, he⟩ := List.mem_map.mp hb
  have hh := streamBlockOutcomes_history _ List.nil tagged ht
  have he' : tagged.2 = b := he
  rw [he', List.take_reverse, hlen] at hh
  have hs : b.history.drop 65535 = tagged.1 := by simpa using hh
  rw [hs, ← he']
  exact ht

end ShorECDLP.Paper2607_13816.ChallengeMigration
