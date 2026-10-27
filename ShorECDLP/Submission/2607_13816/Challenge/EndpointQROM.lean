import ShorECDLP.Submission.«2607_13816».Challenge.EndpointEncoding
import ShorECDLP.Submission.«2607_13816».Challenge.Lookup
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1

/-- Four tag flips turn the infinity row into eight identical zero endpoints. -/
def endpointTagMask (j : Fin 8) (i : Fin 513) : Bool :=
  decide ((j = 0 ∨ j = 3 ∨ j = 5 ∨ j = 6) ∧ i.val = 512)

noncomputable def normalizedEndpointWords {n : Nat} (coeffs : Fin n → PointCoeff)
    (Q : Point) (row : Fin n) (j : Fin 8) (i : Fin 513) : Bool :=
  xor (readEndpointWords coeffs Q row j i)
    (endpointTagMask j i && readConstant coeffs Q ⟨row,.infinity,0⟩)

theorem normalizedEndpointWords_finite {n : Nat} (coeffs : Fin n → PointCoeff)
    (Q : Point) (row : Fin n) {x y : Fp} (hC : curve.toAffine.Nonsingular x y)
    (hrow : constantPoint Q (coeffs row) = .some hC) (j : Fin 8) :
    normalizedEndpointWords coeffs Q row j = readEndpointWords coeffs Q row j := by
  funext i
  have hi : readConstant coeffs Q ⟨row,.infinity,0⟩ = false := by
    simp only [readConstant,hrow,fieldValue,pointCoordinates]
    rfl
  simp only [normalizedEndpointWords,hi,Bool.and_false,Bool.xor_false]

theorem normalizedEndpointWords_infinity {n : Nat} (coeffs : Fin n → PointCoeff)
    (Q : Point) (row : Fin n) (hrow : constantPoint Q (coeffs row) = 0) (j : Fin 8) :
    normalizedEndpointWords coeffs Q row j = fun _ => false := by
  funext i
  by_cases hx : i.val < 256
  · have hn : i.val ≠ 512 := by omega
    fin_cases j <;> simp [normalizedEndpointWords, readEndpointWords, exceptionalEndpointWords,
      endpointFieldWord, hx, endpointTagMask, hn, EndpointBit.read, readConstant, hrow, fieldValue_zero]
  · by_cases hy : i.val < 512
    · have hn : i.val ≠ 512 := by omega
      fin_cases j <;> simp [normalizedEndpointWords, readEndpointWords, exceptionalEndpointWords,
        endpointFieldWord, hx, hy, endpointTagMask, hn, EndpointBit.read, readConstant, hrow, fieldValue_zero]
    · have hi : i = 512 := Fin.ext (by omega)
      subst i
      fin_cases j <;> simp [normalizedEndpointWords, readEndpointWords, exceptionalEndpointWords,
        endpointFieldWord, endpointTagMask, EndpointBit.read, readConstant, hrow, fieldValue_zero]


def endpointSelectGate {n : Nat} (control : Wire) (port : Wire × EndpointBit n) :
    List (TemplateGate n) :=
  match port.2 with
  | .inl false => []
  | .inl true => [.literal (.CX control port.1)]
  | .inr r => [.whenBit r true (.CX control port.1)]

def endpointSelectGates {n : Nat} (control : Wire) (ports : List (Wire × EndpointBit n)) :
    List (TemplateGate n) := ports.flatMap (endpointSelectGate control)

def endpointRawMask {n : Nat} (read : ConstantBit n → Bool)
    (ports : List (Wire × EndpointBit n)) : List Wire :=
  (ports.filter (fun p => EndpointBit.read read p.2)).map Prod.fst

theorem endpointSelectGates_source {n : Nat} (read : ConstantBit n → Bool)
    (control : Wire) (ports : List (Wire × EndpointBit n)) :
    (endpointSelectGates control ports).flatMap (TemplateGate.instantiate read) =
      tableXorGates control (endpointRawMask read ports) := by
  induction ports with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨w,b⟩
    cases b with
    | inl b => cases b <;>
        simpa [endpointSelectGates,endpointSelectGate,TemplateGate.instantiate,
          endpointRawMask,EndpointBit.read,tableXorGates] using ih
    | inr r => cases h : read r <;>
        simpa [endpointSelectGates,endpointSelectGate,TemplateGate.instantiate,
          endpointRawMask,EndpointBit.read,tableXorGates,h] using ih

def endpointTagWires (base : Wire) : List Wire :=
  [endpointRows base 0 512,endpointRows base 3 512,endpointRows base 5 512,endpointRows base 6 512]

def endpointLookupLeaf {n : Nat} (row : Fin n) (base control : Wire) : List (TemplateGate n) :=
  endpointSelectGates control (exceptionalEndpointPorts row (endpointRows base)) ++
    (endpointTagWires base).map (fun w => .whenBit ⟨row,.infinity,0⟩ true (.CX control w))

def endpointLookupLeafCircuit {n : Nat} (read : ConstantBit n → Bool)
    (row : Fin n) (base control : Wire) : Circuit :=
  tableXorGates control (endpointRawMask read (exceptionalEndpointPorts row (endpointRows base))) ++
    tableXorGates control (if read ⟨row,.infinity,0⟩ then endpointTagWires base else [])

theorem endpointLookupLeaf_source {n : Nat} (read : ConstantBit n → Bool)
    (row : Fin n) (base control : Wire) :
    (endpointLookupLeaf row base control).flatMap (TemplateGate.instantiate read) =
      endpointLookupLeafCircuit read row base control := by
  simp only [endpointLookupLeaf, List.flatMap_append, endpointSelectGates_source,
    endpointLookupLeafCircuit]
  congr 1
  cases h : read ⟨row,.infinity,0⟩ <;>
    simp [endpointTagWires, TemplateGate.instantiate, h, tableXorGates]

def endpointLookupProgram {n : Nat} (rows : Nat → Fin n) (base : Wire)
    (tree : UnaryActionTree) (control : Wire) (paths : List Wire) (start : Nat) :
    (count : Nat) × Straight n start (start+count) :=
  let ops := unaryLookupOps (fun l q => endpointLookupLeaf (rows l) base q) tree control paths
  ⟨lookupMeasurements ops, lookupProgram n ops start⟩

theorem endpointLookupProgram_run {n : Nat} (rows : Nat → Fin n) (base : Wire)
    (tree : UnaryActionTree) (control : Wire) (paths : List Wire) (start : Nat)
    (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    compiledRun (endpointLookupProgram rows base tree control paths start) read history =
      (unaryAction .inc (fun l q => endpointLookupLeafCircuit read (rows l) base q)
        tree control paths).run := by
  simp only [endpointLookupProgram, compiledRun, lookupProgram_run, unaryLookupOps_circuit,
    endpointLookupLeaf_source]

theorem endpointLookupProgram_measurements {n : Nat} (rows : Nat → Fin n) (base : Wire)
    (tree : UnaryActionTree) (control : Wire) (paths : List Wire) (start : Nat)
    (hl : tree.Layout control paths) :
    (endpointLookupProgram rows base tree control paths start).1 = tree.internalNodes := by
  exact unaryLookupOps_measurements _ tree control paths hl

/-- Two XOR blocks may overlap; each block is individually duplicate-free. -/
theorem run_endpointXorPair (control : Wire) (a b : List Wire) (s : BasisState)
    (ha : a.Nodup) (hb : b.Nodup) (hca : control ∉ a) (hcb : control ∉ b) :
    Classical.run (tableXorGates control a ++ tableXorGates control b) s =
      tableXorState b (s control) (tableXorState a (s control) s) := by
  rw [Classical.run_append, run_tableXorGates control a s ha hca,
    run_tableXorGates control b _ hb hcb,
    tableXorState_outside a (s control) s control hca]

theorem endpointXorPair_involution (a b : List Wire) (active : Bool) (s : BasisState) :
    tableXorState b active (tableXorState a active
      (tableXorState b active (tableXorState a active s))) = s := by
  funext w
  simp only [tableXorState]
  cases s w <;> cases active <;> cases decide (w ∈ a) <;>
    cases decide (w ∈ b) <;> rfl

theorem endpointXorPair_logical (a b : Nat → List Wire) (tree : UnaryActionTree)
    (active : Bool) (route s : BasisState) :
    tree.runLogicalTree .inc
      (fun label bit state => tableXorState (b label) bit (tableXorState (a label) bit state))
      active route s =
      tableXorState (b (tree.routeLabel route)) active
        (tableXorState (a (tree.routeLabel route)) active s) := by
  induction tree generalizing active s with
  | leaf label => rfl
  | node bit zero one ihz iho =>
    cases active <;> cases hb : route bit <;>
      simp [UnaryActionTree.runLogicalTree,UnaryActionTree.routeLabel,hb,ihz,iho]

theorem endpointXorPair_preserves (a b : Nat → List Wire) (protectedWires : List Wire)
    (ha : ∀ l, (a l).Nodup) (hb : ∀ l, (b l).Nodup)
    (hda : ∀ l w, w ∈ protectedWires → w ∉ a l)
    (hdb : ∀ l w, w ∈ protectedWires → w ∉ b l) :
    UnaryLeafPreserves (fun l q => tableXorGates q (a l) ++ tableXorGates q (b l))
      protectedWires := by
  intro l q hq s w hw
  rw [run_endpointXorPair q _ _ s (ha l) (hb l) (hda l q hq) (hdb l q hq),
    tableXorState_outside _ _ _ w (hdb l w hw),
    tableXorState_outside _ _ _ w (hda l w hw)]

theorem endpointXorPair_coherent (a b : Nat → List Wire) (tree : UnaryActionTree)
    (control : Wire) (paths : List Wire) (hl : tree.Layout control paths)
    (ha : ∀ l, (a l).Nodup) (hb : ∀ l, (b l).Nodup)
    (hda : ∀ l w, w ∈ control::tree.indexWires.dedup++paths → w ∉ a l)
    (hdb : ∀ l w, w ∈ control::tree.indexWires.dedup++paths → w ∉ b l) :
    CoherentlyImplementsOn
      (unaryAction .inc (fun l q => tableXorGates q (a l) ++ tableXorGates q (b l))
        tree control paths)
      (Quantum.run (unaryActionUnitary .inc
        (fun l q => tableXorGates q (a l) ++ tableXorGates q (b l)) tree control paths))
      (Clean paths) := by
  apply unaryAction_coherent _ _ _ _ _ hl
  · exact endpointXorPair_preserves a b _ ha hb hda hdb
  · intro l q g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact tableXorGates_HPFree q (a l) g hg
    · exact tableXorGates_HPFree q (b l) g hg

theorem endpointXorPair_run (a b : Nat → List Wire) (tree : UnaryActionTree)
    (control : Wire) (paths : List Wire) (hl : tree.Layout control paths)
    (ha : ∀ l, (a l).Nodup) (hb : ∀ l, (b l).Nodup)
    (hda : ∀ l w, w ∈ control::tree.indexWires.dedup++paths → w ∉ a l)
    (hdb : ∀ l w, w ∈ control::tree.indexWires.dedup++paths → w ∉ b l)
    (s : BasisState) (hc : Clean paths s) :
    Classical.run (unaryActionUnitary .inc
      (fun l q => tableXorGates q (a l) ++ tableXorGates q (b l)) tree control paths) s =
      tableXorState (b (tree.routeLabel s)) (s control)
        (tableXorState (a (tree.routeLabel s)) (s control) s) := by
  have hrun := run_unaryActionUnitary_as_runLogicalTree .inc
    (fun l q => tableXorGates q (a l) ++ tableXorGates q (b l))
    (fun l q => Classical.run (tableXorGates q (a l) ++ tableXorGates q (b l)))
    (fun l active state => tableXorState (b l) active (tableXorState (a l) active state))
    tree control paths (control::tree.indexWires.dedup++paths) s hl
    (by intro l q state; rfl)
    (by intro l q hq state; exact run_endpointXorPair q _ _ state (ha l) (hb l) (hda l q hq) (hdb l q hq))
    (endpointXorPair_preserves a b _ ha hb hda hdb)
    (by
      intro l active state w hw
      dsimp only
      rw [tableXorState_outside _ _ _ w (hdb l w hw), tableXorState_outside _ _ _ w (hda l w hw)])
    (by intro l active left right h _ w hw; simp only [tableXorState,h w hw])
    (by intro w hw; exact hw) hc
  rw [hrun, endpointXorPair_logical]

theorem endpointRawMask_nodup {n : Nat} (read : ConstantBit n → Bool)
    (ports : List (Wire × EndpointBit n)) (hn : (ports.map Prod.fst).Nodup) :
    (endpointRawMask read ports).Nodup := by
  exact hn.sublist ((List.filter_sublist).map Prod.fst)

theorem endpointTagWires_nodup (base : Wire) : (endpointTagWires base).Nodup := by
  simp [endpointTagWires, endpointRows, matchingRows]

theorem endpointRawMask_mem {n : Nat} (read : ConstantBit n → Bool)
    (ports : List (Wire × EndpointBit n)) (hn : (ports.map Prod.fst).Nodup)
    (w : Wire) (bit : EndpointBit n) (hp : (w,bit) ∈ ports) :
    w ∈ endpointRawMask read ports ↔ EndpointBit.read read bit = true := by
  constructor
  · intro hw
    obtain ⟨p,hp',heq⟩ := List.mem_map.mp hw
    have hm := (List.mem_filter.mp hp').1
    have hb := (List.mem_filter.mp hp').2
    have hi := List.inj_on_of_nodup_map hn hm hp heq
    simpa [hi] using hb
  · intro hb
    exact List.mem_map.mpr ⟨(w,bit),List.mem_filter.mpr ⟨hp,hb⟩,rfl⟩

theorem endpointTagWires_mem (base : Wire) (j : Fin 8) (i : Fin 513) :
    decide (endpointRows base j i ∈ endpointTagWires base) = endpointTagMask j i := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, endpointTagMask]
  fin_cases j <;> simp [endpointTagWires, endpointRows, matchingRows] <;>
    simp only [Wire] at * <;> omega

theorem endpointRawMask_word {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (base : Wire) (j : Fin 8) (i : Fin 513) :
    decide (endpointRows base j i ∈ endpointRawMask (readConstant coeffs Q)
      (exceptionalEndpointPorts row (endpointRows base))) = readEndpointWords coeffs Q row j i := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  apply endpointRawMask_mem _ _ (endpointPortWires_nodup row base)
  apply List.mem_flatten.mpr
  refine ⟨_,List.mem_ofFn.mpr ⟨j,rfl⟩,List.mem_ofFn.mpr ⟨i,rfl⟩⟩

theorem endpointLookupLeaf_word {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (row : Fin n) (base control : Wire) (s : BasisState)
    (hc : control ∉ endpointRawMask (readConstant coeffs Q)
      (exceptionalEndpointPorts row (endpointRows base)))
    (ht : control ∉ endpointTagWires base) (j : Fin 8) (i : Fin 513) :
    Classical.run (endpointLookupLeafCircuit (readConstant coeffs Q) row base control) s
      (endpointRows base j i) =
      xor (s (endpointRows base j i))
        (s control && normalizedEndpointWords coeffs Q row j i) := by
  unfold endpointLookupLeafCircuit
  rw [run_endpointXorPair _ _ _ _ (endpointRawMask_nodup _ _ (endpointPortWires_nodup row base))
    (by split <;> simp [endpointTagWires_nodup]) hc (by split <;> simp_all)]
  simp only [tableXorState, endpointRawMask_word, normalizedEndpointWords]
  cases h : readConstant coeffs Q ⟨row,.infinity,0⟩ <;>
    simp only [Bool.false_eq_true, if_false, List.not_mem_nil, decide_false,
      if_true, endpointTagWires_mem, Bool.and_false, Bool.and_true, Bool.xor_false]
  cases s (endpointRows base j i) <;> cases s control <;>
    cases readEndpointWords coeffs Q row j i <;> cases endpointTagMask j i <;> rfl

theorem endpointRawMask_outside {n : Nat} (read : ConstantBit n → Bool)
    (row : Fin n) (base w : Wire) (hw : w < base ∨ base + 4104 ≤ w) :
    w ∉ endpointRawMask read (exceptionalEndpointPorts row (endpointRows base)) := by
  intro hm
  obtain ⟨p,hp,hpw⟩ := List.mem_map.mp hm
  have hmem : w ∈ (exceptionalEndpointPorts row (endpointRows base)).map Prod.fst :=
    List.mem_map.mpr ⟨p,(List.mem_filter.mp hp).1,hpw⟩
  rw [endpointPortWires] at hmem
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hmem
  simp only [Wire] at *
  omega

theorem endpointTagWires_outside (base w : Wire) (hw : w < base ∨ base + 4104 ≤ w) :
    w ∉ endpointTagWires base := by
  simp [endpointTagWires,endpointRows,matchingRows]
  simp only [Wire] at *
  omega

theorem endpointLookup_coherent {n : Nat} (read : ConstantBit n → Bool)
    (rows : Nat → Fin n) (base : Wire) (tree : UnaryActionTree)
    (control : Wire) (paths : List Wire) (hl : tree.Layout control paths)
    (hd : ∀ w ∈ control::tree.indexWires.dedup++paths, w < base ∨ base+4104 ≤ w) :
    CoherentlyImplementsOn
      (unaryAction .inc (fun l q => endpointLookupLeafCircuit read (rows l) base q)
        tree control paths)
      (Quantum.run (unaryActionUnitary .inc
        (fun l q => endpointLookupLeafCircuit read (rows l) base q) tree control paths))
      (Clean paths) := by
  apply endpointXorPair_coherent _ _ _ _ _ hl
  · intro l
    exact endpointRawMask_nodup _ _ (endpointPortWires_nodup _ _)
  · intro l
    split <;> simp [endpointTagWires_nodup]
  · intro l w hw
    exact endpointRawMask_outside _ _ _ _ (hd w hw)
  · intro l w hw
    split
    · exact endpointTagWires_outside _ _ (hd w hw)
    · simp

theorem endpointLookup_word {n : Nat} (coeffs : Fin n → PointCoeff) (Q : Point)
    (rows : Nat → Fin n) (base : Wire) (tree : UnaryActionTree)
    (control : Wire) (paths : List Wire) (hl : tree.Layout control paths)
    (hd : ∀ w ∈ control::tree.indexWires.dedup++paths, w < base ∨ base+4104 ≤ w)
    (s : BasisState) (hc : Clean paths s) (j : Fin 8) (i : Fin 513) :
    Classical.run (unaryActionUnitary .inc
      (fun l q => endpointLookupLeafCircuit (readConstant coeffs Q) (rows l) base q)
      tree control paths) s (endpointRows base j i) =
      xor (s (endpointRows base j i))
        (s control && normalizedEndpointWords coeffs Q (rows (tree.routeLabel s)) j i) := by
  have hr := endpointXorPair_run
    (fun l => endpointRawMask (readConstant coeffs Q) (exceptionalEndpointPorts (rows l) (endpointRows base)))
    (fun l => if readConstant coeffs Q ⟨rows l,.infinity,0⟩ then endpointTagWires base else [])
    tree control paths hl
    (fun l => endpointRawMask_nodup _ _ (endpointPortWires_nodup _ _))
    (by intro l; dsimp only; split <;> simp [endpointTagWires_nodup])
    (by intro l w hw; exact endpointRawMask_outside _ _ _ _ (hd w hw))
    (by intro l w hw; dsimp only; split; exact endpointTagWires_outside _ _ (hd w hw); simp) s hc
  dsimp only at hr
  unfold endpointLookupLeafCircuit
  rw [hr]
  have ht := endpointLookupLeaf_word coeffs Q (rows (tree.routeLabel s)) base control s
    (endpointRawMask_outside _ _ _ _ (hd control (by simp)))
    (endpointTagWires_outside _ _ (hd control (by simp))) j i
  unfold endpointLookupLeafCircuit at ht
  rw [run_endpointXorPair _ _ _ _
    (endpointRawMask_nodup _ _ (endpointPortWires_nodup _ _))
    (by split <;> simp [endpointTagWires_nodup])
    (endpointRawMask_outside _ _ _ _ (hd control (by simp)))
    (by split; exact endpointTagWires_outside _ _ (hd control (by simp)); simp)] at ht
  exact ht

theorem endpointXorPair_frame (a b : Nat → List Wire) (tree : UnaryActionTree)
    (control : Wire) (paths : List Wire) (hl : tree.Layout control paths)
    (ha : ∀ l, (a l).Nodup) (hb : ∀ l, (b l).Nodup)
    (hda : ∀ l w, w ∈ control::tree.indexWires.dedup++paths → w ∉ a l)
    (hdb : ∀ l w, w ∈ control::tree.indexWires.dedup++paths → w ∉ b l)
    (s : BasisState) (hc : Clean paths s) (w : Wire)
    (hwa : ∀ l, w ∉ a l) (hwb : ∀ l, w ∉ b l) :
    Classical.run (unaryActionUnitary .inc
      (fun l q => tableXorGates q (a l) ++ tableXorGates q (b l)) tree control paths) s w = s w := by
  rw [endpointXorPair_run a b tree control paths hl ha hb hda hdb s hc,
    tableXorState_outside _ _ _ w (hwb _), tableXorState_outside _ _ _ w (hwa _)]

theorem endpointXorPair_unload (a b : Nat → List Wire) (tree : UnaryActionTree)
    (control : Wire) (paths : List Wire) (hl : tree.Layout control paths)
    (ha : ∀ l, (a l).Nodup) (hb : ∀ l, (b l).Nodup)
    (hda : ∀ l w, w ∈ control::tree.indexWires.dedup++paths → w ∉ a l)
    (hdb : ∀ l w, w ∈ control::tree.indexWires.dedup++paths → w ∉ b l)
    (s : BasisState) (hc : Clean paths s) :
    let circuit := unaryActionUnitary .inc
      (fun l q => tableXorGates q (a l) ++ tableXorGates q (b l)) tree control paths
    Classical.run circuit (Classical.run circuit s) = s := by
  dsimp only
  let circuit := unaryActionUnitary .inc
    (fun l q => tableXorGates q (a l) ++ tableXorGates q (b l)) tree control paths
  let loaded := Classical.run circuit s
  have hf (w : Wire) (hw : w ∈ control::tree.indexWires.dedup++paths) : loaded w = s w :=
    endpointXorPair_frame a b tree control paths hl ha hb hda hdb s hc w
      (fun l => hda l w hw) (fun l => hdb l w hw)
  have hclean : Clean paths loaded := by
    intro w hw
    rw [hf w (by simp [hw])]
    exact hc w hw
  have hr : tree.routeLabel loaded = tree.routeLabel s := by
    apply UnaryActionTree.routeLabel_congr
    intro w hw
    exact hf w (by simp [hw])
  have hcontrol : loaded control = s control := hf control (by simp)
  change Classical.run circuit loaded = s
  rw [endpointXorPair_run a b tree control paths hl ha hb hda hdb loaded hclean,hr,hcontrol]
  dsimp only [loaded,circuit]
  rw [endpointXorPair_run a b tree control paths hl ha hb hda hdb s hc]
  exact endpointXorPair_involution _ _ _ _

theorem endpointLookup_wellFormed {n : Nat} (read : ConstantBit n → Bool)
    (rows : Nat → Fin n) (base : Wire) (tree : UnaryActionTree)
    (control : Wire) (paths : List Wire) (hl : tree.Layout control paths)
    (hd : ∀ w ∈ control::tree.indexWires.dedup++paths, w < base ∨ base+4104 ≤ w) :
    (unaryAction .inc (fun l q => endpointLookupLeafCircuit read (rows l) base q)
      tree control paths).WellFormed := by
  apply unaryAction_wellFormed _ _ _ _ _ hl
  intro l _ q hq g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact tableXorGates_wellFormed q _ (endpointRawMask_outside _ _ _ _ (hd q hq)) g hg
  · apply tableXorGates_wellFormed q _ ?_ g hg
    split
    · exact endpointTagWires_outside _ _ (hd q hq)
    · simp

theorem endpointLookup_tCount {n : Nat} (read : ConstantBit n → Bool)
    (rows : Nat → Fin n) (base : Wire) (tree : UnaryActionTree)
    (control : Wire) (paths : List Wire) (hl : tree.Layout control paths) :
    (unaryAction .inc (fun l q => endpointLookupLeafCircuit read (rows l) base q)
      tree control paths).tCount = 7 * tree.internalNodes := by
  rw [unaryAction_tCount _ _ _ _ _ hl]
  have hz (t : UnaryActionTree) (q : Wire) (ws : List Wire) :
      t.leafCostSum (fun l wire => ShorECDLP.tCount (endpointLookupLeafCircuit read (rows l) base wire)) q ws = 0 := by
    induction t generalizing q ws with
    | leaf l => simp [UnaryActionTree.leafCostSum,endpointLookupLeafCircuit,tCount_append]
    | node bit zero one ihz iho =>
      cases ws <;> simp only [UnaryActionTree.leafCostSum,ihz,iho,zero_add]
  rw [hz,zero_add]

theorem endpointSelectGates_length {n : Nat} (control : Wire)
    (ports : List (Wire × EndpointBit n)) :
    (endpointSelectGates control ports).length ≤ ports.length := by
  induction ports with
  | nil => rfl
  | cons p ps ih =>
    have hp : (endpointSelectGate control p).length ≤ 1 := by
      rcases p with ⟨w,b⟩
      cases b with
      | inl b => cases b <;> simp only [endpointSelectGate,List.length_nil,List.length_cons] <;> omega
      | inr r => rfl
    simp only [endpointSelectGates,List.flatMap_cons,List.length_append,List.length_cons] at *
    omega

theorem endpointLookupLeaf_length {n : Nat} (row : Fin n) (base control : Wire) :
    (endpointLookupLeaf row base control).length ≤ 4108 := by
  have h := endpointSelectGates_length control (exceptionalEndpointPorts row (endpointRows base))
  have hp : (exceptionalEndpointPorts row (endpointRows base)).length = 4104 := by
    exact exceptionalEndpointPorts_length row (endpointRows base)
  simp only [endpointLookupLeaf,List.length_append,List.length_map]
  have ht : (endpointTagWires base).length = 4 := rfl
  omega

end ShorECDLP.Paper2607_13816.ChallengeMigration
