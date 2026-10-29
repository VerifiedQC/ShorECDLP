import ShorECDLP.Submission.«2607_13816».Challenge.EEAScheduleSlots
import ShorECDLP.Submission.«2607_13816».Challenge.OuterResources
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

/-- Every mentioned wire, including disabled constant-controlled gates. -/
def templateGateWires {n : Nat} : TemplateGate n → List Wire
  | .literal g => gateWires g
  | .whenBit _ _ g => gateWires g

/-- Syntactic support includes measurement targets and all record-controlled gates. -/
def straightWires {n s e : Nat} : Straight n s e → List Wire
  | .done => []
  | .gate g p => templateGateWires g ++ straightWires p
  | .recordGate _ _ g p => gateWires g ++ straightWires p
  | .measure w p => w :: straightWires p

private theorem subset_append {a b c d : List Wire} (h : a ⊆ c) (k : b ⊆ d) :
    a ++ b ⊆ c ++ d := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact List.mem_append_left _ (h hx)
  · exact List.mem_append_right _ (k hx)

theorem templateGate_instantiate_support {n : Nat} (g : TemplateGate n)
    (read : ConstantBit n → Bool) : circuitWires (g.instantiate read) ⊆ templateGateWires g := by
  cases g <;> simp only [TemplateGate.instantiate,templateGateWires]
  · simp [circuitWires]
  · split <;> simp [circuitWires]

theorem straight_instantiate_support {n s e : Nat} (p : Straight n s e)
    (read : ConstantBit n → Bool) (history : Fin s → Bool) :
    (p.instantiate read history).wires ⊆ straightWires p := by
  induction p with
  | done => exact List.Subset.refl _
  | gate g p ih =>
    exact subset_append (templateGate_instantiate_support g read) (ih history)
  | recordGate i v g p ih =>
    simp only [Straight.instantiate,AdaptiveCircuit.wires,straightWires]
    apply subset_append _ (ih history)
    split <;> simp [circuitWires]
  | measure w p ih =>
    intro x hx
    simp only [Straight.instantiate,AdaptiveCircuit.wires,List.mem_cons,List.mem_append] at hx
    rcases hx with rfl | hx | hx
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih _ hx)
    · exact List.mem_cons_of_mem _ (ih _ hx)

theorem straightWires_append {n a b c : Nat} (p : Straight n a b) (q : Straight n b c) :
    straightWires (p.append q)=straightWires p ++ straightWires q := by
  induction p <;> simp_all only [Straight.append,straightWires,List.nil_append,List.append_assoc,List.cons_append]

theorem straightWires_castFinish {n s e f : Nat} (h : e=f) (p : Straight n s e) :
    straightWires (castFinish h p)=straightWires p := by subst f; rfl

theorem straightWires_shift {n s e : Nat} (p : Straight n s e) (offset : Nat) :
    straightWires (shiftStraight offset p)=straightWires p := by
  induction p <;> simp_all only [shiftStraight,straightWires]

theorem templateGateWires_reindex {n m : Nat} (f : Fin n → Fin m) (g : TemplateGate n) :
    templateGateWires (reindexGate f g)=templateGateWires g := by cases g <;> rfl

theorem straightWires_reindex {n m s e : Nat} (f : Fin n → Fin m) (p : Straight n s e) :
    straightWires (reindexStraight f p)=straightWires p := by
  induction p <;> simp_all only [reindexStraight,straightWires,templateGateWires_reindex]

theorem gateProgram_support {n s : Nat} (gs : List (TemplateGate n)) :
    straightWires (gateProgram (cursor := s) gs)=gs.flatMap templateGateWires := by
  induction gs <;> simp_all only [gateProgram,straightWires,List.flatMap_nil,List.flatMap_cons]

theorem literalProgram_support (n start : Nat) (gs : Circuit) :
    straightWires (literalProgram (n := n) (s := start) gs)=circuitWires gs := by
  simp only [literalProgram,gateProgram_support,List.flatMap_map,templateGateWires,circuitWires]

theorem recordGates_support {n s e : Nat} (i : Fin s) (gs : Circuit) (p : Straight n s e) :
    straightWires (recordGates i gs p)=circuitWires gs ++ straightWires p := by
  induction gs <;> simp_all only [recordGates,straightWires,circuitWires,List.flatMap_nil,List.flatMap_cons,List.nil_append,List.append_assoc]

theorem appendCompiled_support {n start : Nat} (p : (count : Nat) × Straight n start (start+count))
    (q : (count : Nat) × Straight n (start+p.1) (start+p.1+count)) :
    straightWires (appendCompiled p q).2=straightWires p.2 ++ straightWires q.2 := by
  simp only [appendCompiled,straightWires_castFinish,straightWires_append]

theorem surroundCompiled_support {n start : Nat} (before after : Circuit)
    (p : (count : Nat) × Straight n start (start+count)) :
    straightWires (surroundCompiled before after p).2=
      circuitWires before ++ straightWires p.2 ++ circuitWires after := by
  simp only [surroundCompiled,prependCompiled,appendCompiled_support,straightWires_append,literalProgram_support,List.append_assoc]


theorem templateGateWires_relabel {n : Nat} (e : Wire ≃ Wire) (g : TemplateGate n) :
    templateGateWires (relabelTemplateGate e g)=(templateGateWires g).map e := by
  cases g <;> rename_i g <;> cases g <;> rfl

theorem straightWires_relabel {n s t : Nat} (e : Wire ≃ Wire) (p : Straight n s t) :
    straightWires (relabelStraight e p)=(straightWires p).map e := by
  have hg (g : Gate) : gateWires (g.relabel e)=(gateWires g).map e := by cases g <;> rfl
  induction p <;> simp_all only [relabelStraight,straightWires,templateGateWires_relabel,List.map_nil,List.map_append,List.map_cons]

theorem reindexCompiled_support {n m start : Nat} (f : Fin n → Fin m)
    (p : (count : Nat) × Straight n start (start+count)) :
    straightWires (reindexCompiled f p).2=straightWires p.2 := by
  exact straightWires_reindex f p.2

theorem relabelCompiled_support {n start : Nat} (e : Wire ≃ Wire)
    (p : (count : Nat) × Straight n start (start+count)) :
    straightWires (relabelCompiled e p).2=(straightWires p.2).map e := by
  exact straightWires_relabel e p.2

theorem sequenceProgram_support (n : Nat) (ps : List (FixedSegment n)) (support : List Wire)
    (h : ∀ p ∈ ps, ∀ start, straightWires (p start).2 ⊆ support) (start : Nat) :
    straightWires (sequenceProgram n ps start).2 ⊆ support := by
  induction ps generalizing start with
  | nil => exact List.nil_subset _
  | cons p ps ih =>
    simp only [sequenceProgram,appendCompiled_support]
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact h p (by simp) start hw
    · exact ih (fun p hp => h p (by simp [hp])) _ hw

theorem collectProgram_support (n : Nat)
    (next : (cursor : Nat) → List (Fin cursor) → (count : Nat) × Straight n cursor (cursor+count))
    (support : List Wire) (h : ∀ cursor prior, straightWires (next cursor prior).2 ⊆ support)
    (ws : List Wire) (hw : ws ⊆ support) (start : Nat) (prior : List (Fin start)) :
    straightWires (collectProgram n next ws start prior).2 ⊆ support := by
  induction ws generalizing start with
  | nil => exact h start prior
  | cons w ws ih =>
    simp only [collectProgram,straightWires_castFinish,straightWires,List.cons_subset]
    exact ⟨hw List.mem_cons_self,ih (fun _ hx => hw (List.mem_cons_of_mem _ hx)) _ _⟩

theorem resetProgram_support_static (n start : Nat) (ws : List Wire) :
    straightWires (resetProgram n start ws)=ws := by
  induction ws generalizing start <;> simp_all only [resetProgram,straightWires_castFinish,straightWires]

/-- A syntactic allocation is a sound support certificate for every readout and
history, including disabled constant gates and both measurement outcomes. -/
theorem compiled_support_of_static {n start : Nat}
    (p : (count : Nat) × Straight n start (start+count)) (support : List Wire)
    (hp : straightWires p.2 ⊆ support) (read : ConstantBit n → Bool) (history : Fin start → Bool) :
    (p.2.instantiate read history).wires ⊆ support :=
  (straight_instantiate_support p.2 read history).trans hp


def lookupOpWires {n : Nat} : LookupOp n → List Wire
  | .gates gs => gs.flatMap templateGateWires
  | .erase a b t => t :: circuitWires (controlledZ a b)

theorem lookupProgram_support (n : Nat) (ops : List (LookupOp n)) (start : Nat) :
    straightWires (lookupProgram n ops start)=ops.flatMap lookupOpWires := by
  induction ops generalizing start with
  | nil => rfl
  | cons op ops ih =>
    cases op <;> simp only [lookupProgram,straightWires_castFinish,straightWires_append,
      gateProgram_support,andEraseProgram,straightWires,recordGates_support,List.append_nil,
      List.flatMap_cons,lookupOpWires,ih]

theorem ordinaryOp_support {n : Nat} (gs : Circuit) :
    lookupOpWires (@ordinaryOp n gs)=circuitWires gs := by
  simp only [ordinaryOp,lookupOpWires,List.flatMap_map,templateGateWires,circuitWires]

theorem unaryLookupOps_support {n : Nat} (leaf : Nat → Wire → List (TemplateGate n))
    (tree : UnaryActionTree) (q : Wire) (paths support : List Wire)
    (hq : q ∈ support) (hp : paths ⊆ support) (hb : tree.indexWires ⊆ support)
    (hl : ∀ l c, c ∈ support → (leaf l c).flatMap templateGateWires ⊆ support) :
    ∀ op ∈ unaryLookupOps leaf tree q paths, lookupOpWires op ⊆ support := by
  induction tree generalizing q paths with
  | leaf l => simpa only [unaryLookupOps,List.forall_mem_singleton,lookupOpWires] using hl l q hq
  | node bit zero one ihz iho =>
    cases paths with
    | nil => simp [unaryLookupOps]
    | cons path rest =>
      have hpath := hp List.mem_cons_self
      have hrest : rest ⊆ support := fun _ hx => hp (List.mem_cons_of_mem _ hx)
      have hbit : bit ∈ support := hb List.mem_cons_self
      have hz : zero.indexWires ⊆ support := fun _ hx => hb (List.mem_cons_of_mem _ (List.mem_append_left _ hx))
      have ho : one.indexWires ⊆ support := fun _ hx => hb (List.mem_cons_of_mem _ (List.mem_append_right _ hx))
      have hz' := ihz path rest hpath hrest hz
      have ho' := iho path rest hpath hrest ho
      simp only [unaryLookupOps,List.forall_mem_append,List.forall_mem_cons,List.mem_nil_iff,false_implies]
      refine ⟨⟨⟨⟨⟨?_,fun _ => trivial⟩,hz'⟩,⟨?_,fun _ => trivial⟩⟩,ho'⟩,?_,?_,?_,?_,fun _ => trivial⟩
      all_goals simp [ordinaryOp,templateGateWires,lookupOpWires,computeZeroAnd,controlledZ,circuitWires,gateWires,hbit,hq,hpath]

theorem lookupLeafGates_support {n : Nat} (q : Wire) (ports : List (ConstantBit n × Wire))
    (support : List Wire) (hq : q ∈ support) (hp : ∀ p ∈ ports, p.2 ∈ support) :
    (lookupLeafGates q ports).flatMap templateGateWires ⊆ support := by
  intro w hw
  simp only [lookupLeafGates,List.flatMap_map,List.mem_flatMap] at hw
  obtain ⟨p,hp',hw⟩ := hw
  simp only [templateGateWires,gateWires,List.mem_cons,List.mem_nil_iff,or_false] at hw
  rcases hw with rfl | rfl
  · exact hq
  · exact hp p hp'

theorem pointLeaf_support {n : Nat} (row : Fin n) (q : Wire) (support : List Wire)
    (hq : q ∈ support) (hp : pointLogicalWires ⊆ support) :
    (pointLeaf row q).flatMap templateGateWires ⊆ support := by
  apply lookupLeafGates_support q _ support hq
  intro p hp'
  exact hp (List.of_mem_zip hp').2

theorem firstLookupOps_support : ∀ op ∈ firstLookupOps, lookupOpWires op ⊆ resetWires := by
  apply unaryLookupOps_support
  · simp [resetWires]
  · intro w hw
    apply List.mem_append_left
    apply List.mem_append_left
    simp only [List.mem_range'_1] at hw
    simp only [List.mem_range]
    omega
  · intro w hw
    have h := (tableAddressTree_mem_index (List.range' 855 16) 0 1 w).mp hw
    exact List.mem_append_right _ h
  · intro l q hq
    apply pointLeaf_support _ q resetWires hq
    intro w hw
    simp only [pointLogicalWires,pointCorrectionX,pointCorrectionYInf,List.mem_append,
      List.mem_range'_1,List.mem_cons,List.mem_nil_iff,or_false] at hw
    simp only [resetWires,List.mem_append,List.mem_range,List.mem_singleton,List.mem_range'_1]
    rcases hw with hw | hw | hw
    · exact Or.inl (Or.inl (by omega))
    · exact Or.inl (Or.inl (by omega))
    · exact Or.inl (Or.inr hw)

theorem actualFirstWindow_support_static (start : Nat) :
    straightWires (actualFirstWindow.program start) ⊆ resetWires := by
  simp only [actualFirstWindow,straightWires_reindex,firstLookupProgram,
    straightWires_castFinish,lookupProgram_support]
  intro w hw
  obtain ⟨op,hop,hw⟩ := List.mem_flatMap.mp hw
  exact firstLookupOps_support op hop hw

end ShorECDLP.Paper2607_13816.ChallengeMigration
