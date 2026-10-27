import ShorECDLP.Submission.«2607_13816».Challenge.EndpointCoherent
import ShorECDLP.Submission.«2607_13816».Challenge.SharedTable
import ShorECDLP.Submission.«2607_13816».Challenge.Outer
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Classical Quantum ShorECDLP.Challenge ShorECDLP.Secp256k1

/-- Four source words, one reusable target word, then the data word. -/
def batchWord (base : Wire) (j : Fin 6) (i : Fin 513) : Wire := base + 513*j.val+i.val
def batchFlag (base : Wire) : Wire := base+3078
def batchScratch (base : Wire) : List Wire := List.ofFn (fun i : Fin 511 => base+3079+i.val)

def batchSelection (sources : Bool) (target : Fin 4) : List (Fin 8 × Fin 5) :=
  (if sources then [(0,0),(1,1),(2,2),(3,3)] else []) ++ [(⟨4+target.val,by omega⟩,4)]

def batchPorts {n : Nat} (row : Fin n) (base : Wire) (selection : List (Fin 8 × Fin 5)) :
    List (Wire × EndpointBit n) :=
  selection.flatMap fun p => List.ofFn fun i : Fin 513 =>
    (batchWord base p.2.castSucc i, exceptionalEndpointWords row p.1 i)

def batchTags (base : Wire) (selection : List (Fin 8 × Fin 5)) : List Wire :=
  (selection.filter (fun p => endpointTagMask p.1 512)).map fun p => batchWord base p.2.castSucc 512

def batchLeaf {n : Nat} (row : Fin n) (base control : Wire) (selection : List (Fin 8 × Fin 5)) :
    List (TemplateGate n) :=
  endpointSelectGates control (batchPorts row base selection) ++
    (batchTags base selection).map (fun w => .whenBit ⟨row,.infinity,0⟩ true (.CX control w))

def batchLeafCircuit {n : Nat} (read : ConstantBit n → Bool) (row : Fin n)
    (base control : Wire) (selection : List (Fin 8 × Fin 5)) : Circuit :=
  tableXorGates control (endpointRawMask read (batchPorts row base selection)) ++
    tableXorGates control (if read ⟨row,.infinity,0⟩ then batchTags base selection else [])

theorem batchLeaf_source {n : Nat} (read : ConstantBit n → Bool) (row : Fin n)
    (base control : Wire) (selection : List (Fin 8 × Fin 5)) :
    (batchLeaf row base control selection).flatMap (TemplateGate.instantiate read) =
      batchLeafCircuit read row base control selection := by
  simp only [batchLeaf, List.flatMap_append, endpointSelectGates_source, batchLeafCircuit]
  congr 1
  cases h : read ⟨row,.infinity,0⟩ <;> simp only [List.flatMap_map,TemplateGate.instantiate,h,
    Bool.false_eq_true,ite_false,ite_true,tableXorGates,List.map_nil]
  all_goals induction batchTags base selection <;> simp_all

inductive BatchOp where
  | query (sources : Bool) (target : Fin 4)
  | swap (source : Fin 4) (target : Fin 6)

/-- Seven target lifetimes. Source loading shares the first query; source
unloading shares the last query, after every source has been restored. -/
def batchSchedule : List BatchOp :=
  [.query true 3, .swap 3 2, .swap 3 1, .swap 3 0, .swap 3 5, .query false 3,
   .query false 2, .swap 2 1, .swap 2 0, .swap 2 5, .query false 2,
   .query false 1, .swap 1 0, .swap 1 5, .query false 1,
   .query false 0, .swap 0 5, .query false 0,
   .query false 1, .swap 1 0, .query false 1,
   .query false 2, .swap 2 0, .swap 2 1, .query false 2,
   .query false 3, .swap 3 0, .swap 3 1, .swap 3 2, .query true 3]

def batchQueries : List BatchOp → Nat
  | [] => 0
  | .query _ _ :: xs => 1+batchQueries xs
  | .swap _ _ :: xs => batchQueries xs

theorem batchSchedule_queries : batchQueries batchSchedule = 14 := rfl

def batchOpCircuit (base : Wire) (source : Fin 4) (target : Fin 6) : Circuit :=
  endpointTranspositionCircuit (batchWord base ⟨source.val,by omega⟩)
    (batchWord base 4) (batchWord base target) (batchFlag base) (batchScratch base)

def batchOps {n : Nat} (rows : Nat → Fin n) (base : Wire) (tree : UnaryActionTree)
    (control : Wire) (paths : List Wire) : List BatchOp → List (LookupOp n)
  | [] => []
  | .query sources target :: xs =>
    unaryLookupOps (fun l q => batchLeaf (rows l) base q (batchSelection sources target)) tree control paths ++
      batchOps rows base tree control paths xs
  | .swap source target :: xs => ordinaryOp (batchOpCircuit base source target) ::
      batchOps rows base tree control paths xs

theorem batchOps_measurements {n : Nat} (rows : Nat → Fin n) (base : Wire) (tree : UnaryActionTree)
    (control : Wire) (paths : List Wire) (hl : tree.Layout control paths) (ops : List BatchOp) :
    lookupMeasurements (batchOps rows base tree control paths ops) = batchQueries ops * tree.internalNodes := by
  induction ops with
  | nil => simp [batchOps, lookupMeasurements, batchQueries]
  | cons op xs ih =>
    cases op with
    | query sources target =>
      simp only [batchOps, lookupMeasurements_append, unaryLookupOps_measurements _ _ _ _ hl,
        ih, batchQueries, Nat.add_mul, Nat.one_mul]
    | swap source target => exact ih

noncomputable def batchSource {n : Nat} (read : ConstantBit n → Bool) (rows : Nat → Fin n)
    (base : Wire) (tree : UnaryActionTree) (control : Wire) (paths : List Wire) : List BatchOp → AdaptiveCircuit
  | [] => .done
  | .query sources target :: xs =>
    (unaryAction .inc (fun l q => batchLeafCircuit read (rows l) base q (batchSelection sources target))
      tree control paths).seq (batchSource read rows base tree control paths xs)
  | .swap source target :: xs =>
    .unitary (batchOpCircuit base source target) (batchSource read rows base tree control paths xs)

theorem batchOps_source {n : Nat} (read : ConstantBit n → Bool) (rows : Nat → Fin n)
    (base : Wire) (tree : UnaryActionTree) (control : Wire) (paths : List Wire) (ops : List BatchOp) :
    lookupCircuit read (batchOps rows base tree control paths ops) =
      batchSource read rows base tree control paths ops := by
  induction ops with
  | nil => rfl
  | cons op xs ih =>
    cases op with
    | query sources target =>
      simp only [batchOps,lookupCircuit_append,unaryLookupOps_circuit,batchLeaf_source,ih,batchSource]
    | swap source target => simp only [batchOps,ordinaryOp,lookupCircuit,literal_gates,ih,batchSource]

def batchedEndpointProgram {n : Nat} (rows : Nat → Fin n) (base : Wire) (tree : UnaryActionTree)
    (control : Wire) (paths : List Wire) (start : Nat) :
    (count : Nat) × Straight n start (start+count) :=
  ⟨lookupMeasurements (batchOps rows base tree control paths batchSchedule),
    lookupProgram n (batchOps rows base tree control paths batchSchedule) start⟩

theorem batchedEndpointProgram_run {n : Nat} (read : ConstantBit n → Bool) (rows : Nat → Fin n)
    (base : Wire) (tree : UnaryActionTree) (control : Wire) (paths : List Wire) (start : Nat)
    (history : Fin start → Bool) :
    compiledRun (batchedEndpointProgram rows base tree control paths start) read history =
      (batchSource read rows base tree control paths batchSchedule).run := by
  simp only [batchedEndpointProgram,compiledRun,lookupProgram_run,batchOps_source]

theorem batchedEndpointProgram_count {n : Nat} (rows : Nat → Fin n) (base : Wire)
    (tree : UnaryActionTree) (control : Wire) (paths : List Wire) (start : Nat)
    (hl : tree.Layout control paths) :
    (batchedEndpointProgram rows base tree control paths start).1 = 14 * tree.internalNodes := by
  exact (batchOps_measurements rows base tree control paths hl batchSchedule).trans
    (congrArg (fun k => k*tree.internalNodes) batchSchedule_queries)

def batchedEndpointWindow {n : Nat} (rows : Nat → Fin n) (base : Wire) (tree : UnaryActionTree)
    (control : Wire) (paths : List Wire) (hl : tree.Layout control paths) : OuterWindow n :=
  ⟨14*tree.internalNodes,fun start => castFinish
    (by rw [batchedEndpointProgram_count rows base tree control paths start hl])
    (batchedEndpointProgram rows base tree control paths start).2⟩
end ShorECDLP.Paper2607_13816.ChallengeMigration
