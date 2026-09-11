import ShorECDLP.Submission.«2607_13816».EEA.AdaptiveSupport
/-!
# Measured table lookup

A complete little-endian unary tree loads one constant table mask by XOR.
The same physical adaptive lookup clears that load coherently. All path wires
are restored, and support/count certificates include measurement corrections.
The 16-bit resource certificate is for this lookup alone, not the full oracle.
-/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section
/-- XOR the selected constant bits into a target register under one physical control. -/
def tableXorGates (control : Wire) (selected : List Wire) : Circuit :=
  selected.map (Gate.CX control)

def tableXorState (selected : List Wire) (active : Bool) (s : BasisState) : BasisState :=
  fun w => s w ^^ (active && decide (w∈selected))

theorem run_tableXorGates (control : Wire) (selected : List Wire) (s : BasisState)
    (hn : selected.Nodup) (hc : control∉selected) :
    Classical.run (tableXorGates control selected) s=tableXorState selected (s control) s := by
  induction selected generalizing s with
  | nil =>
    change s=tableXorState List.nil (s control) s
    funext w
    simp [tableXorState]
  | cons t ts ih =>
    have ht : t∉ts := (List.nodup_cons.mp hn).1
    have hct : control≠t := by intro h; exact hc (by simp [h])
    have hcs : control∉ts := by intro h; exact hc (by simp [h])
    simp only [tableXorGates,List.map_cons,Classical.run_cons,Classical.applyGate]
    rw [show List.map (Gate.CX control) ts=tableXorGates control ts from rfl,
      ih _ (List.nodup_cons.mp hn).2 hcs]
    funext w
    by_cases hw : w=t
    · subst w
      simp [tableXorState,upd,hct,ht]
    · simp [tableXorState,upd,hw,hct]

@[simp] theorem tableXorState_false (selected : List Wire) (s : BasisState) :
    tableXorState selected false s=s := by
  funext w
  simp [tableXorState]

theorem tableXorState_outside (selected : List Wire) (active : Bool) (s : BasisState)
    (w : Wire) (hw : w∉selected) : tableXorState selected active s w=s w := by
  simp [tableXorState,hw]

theorem tableXorState_involution (selected : List Wire) (active : Bool) (s : BasisState) :
    tableXorState selected active (tableXorState selected active s)=s := by
  funext w
  simp [tableXorState]

theorem tableXorGates_HPFree (control : Wire) (selected : List Wire) :
    HPFree (tableXorGates control selected) := by
  intro g hg
  obtain ⟨w,_,rfl⟩ := List.mem_map.mp hg
  simp [IsClassicalGate]

theorem tableXorGates_wellFormed (control : Wire) (selected : List Wire) (hc : control∉selected) :
    CircuitWellFormed (tableXorGates control selected) := by
  intro g hg
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hg
  exact fun h => hc (h ▸ hw)

def tableLookup (mask : Nat → List Wire) (tree : UnaryActionTree) (control : Wire)
    (ancillas : List Wire) : AdaptiveCircuit :=
  unaryAction .inc (fun label q => tableXorGates q (mask label)) tree control ancillas

theorem tableLookup_logical (mask : Nat → List Wire) (tree : UnaryActionTree)
    (active : Bool) (route s : BasisState) :
    tree.runLogicalTree .inc (fun label b => tableXorState (mask label) b) active route s =
      tableXorState (mask (tree.routeLabel route)) active s := by
  induction tree generalizing active s with
  | leaf label => rfl
  | node bit zero one ihz iho =>
    cases active <;> cases hb : route bit <;>
      simp [UnaryActionTree.runLogicalTree,UnaryActionTree.routeLabel,hb,ihz,iho]

private theorem tableLookup_preserves (mask : Nat → List Wire) (protectedWires : List Wire)
    (hn : ∀ label, (mask label).Nodup)
    (hd : ∀ label w, w∈protectedWires → w∉mask label) :
    UnaryLeafPreserves (fun label q => tableXorGates q (mask label)) protectedWires := by
  intro label q hq s w hw
  rw [run_tableXorGates q _ s (hn label) (hd label q hq)]
  exact tableXorState_outside _ _ _ _ (hd label w hw)

theorem tableLookup_coherent (mask : Nat → List Wire) (tree : UnaryActionTree)
    (control : Wire) (ancillas : List Wire) (hl : tree.Layout control ancillas)
    (hn : ∀ label, (mask label).Nodup)
    (hd : ∀ label w, w∈control::tree.indexWires.dedup++ancillas → w∉mask label) :
    CoherentlyImplementsOn (tableLookup mask tree control ancillas)
      (Quantum.run (unaryActionUnitary .inc (fun label q => tableXorGates q (mask label))
        tree control ancillas)) (Clean ancillas) := by
  apply unaryAction_coherent _ _ _ _ _ hl
  · exact tableLookup_preserves mask _ hn hd
  · intro label q
    exact tableXorGates_HPFree q (mask label)

theorem tableLookup_run (mask : Nat → List Wire) (tree : UnaryActionTree)
    (control : Wire) (ancillas : List Wire) (hl : tree.Layout control ancillas)
    (hn : ∀ label, (mask label).Nodup)
    (hd : ∀ label w, w∈control::tree.indexWires.dedup++ancillas → w∉mask label)
    (s : BasisState) (hc : Clean ancillas s) :
    Classical.run (unaryActionUnitary .inc (fun label q => tableXorGates q (mask label))
      tree control ancillas) s = tableXorState (mask (tree.routeLabel s)) (s control) s := by
  have hrun := run_unaryActionUnitary_as_runLogicalTree .inc
    (fun label q => tableXorGates q (mask label))
    (fun label q => Classical.run (tableXorGates q (mask label)))
    (fun label active => tableXorState (mask label) active)
    tree control ancillas (control::tree.indexWires.dedup++ancillas) s hl
    (by intro label q state; rfl)
    (by intro label q hq state; exact run_tableXorGates q _ state (hn label) (hd label q hq))
    (tableLookup_preserves mask _ hn hd)
    (by intro label active state w hw; exact tableXorState_outside _ _ _ _ (hd label w hw))
    (by
      intro label active left right h _ w hw
      simp only [tableXorState,h w hw])
    (by intro w hw; exact hw) hc
  rw [hrun,tableLookup_logical]

theorem tableLookup_wellFormed (mask : Nat → List Wire) (tree : UnaryActionTree)
    (control : Wire) (ancillas : List Wire) (hl : tree.Layout control ancillas)
    (hd : ∀ label w, w∈control::tree.indexWires.dedup++ancillas → w∉mask label) :
    (tableLookup mask tree control ancillas).WellFormed := by
  apply unaryAction_wellFormed _ _ _ _ _ hl
  intro label _ q hq
  exact tableXorGates_wellFormed q _ (hd label q hq)

@[simp] theorem tableXorGates_tCount (control : Wire) (selected : List Wire) :
    ShorECDLP.tCount (tableXorGates control selected)=0 := by
  induction selected with
  | nil => rfl
  | cons w ws ih => simpa [tableXorGates,tCount,tCost] using ih

theorem tableLookup_tCount (mask : Nat → List Wire) (tree : UnaryActionTree)
    (control : Wire) (ancillas : List Wire) (hl : tree.Layout control ancillas) :
    (tableLookup mask tree control ancillas).tCount=7*tree.internalNodes := by
  rw [tableLookup,unaryAction_tCount _ _ _ _ _ hl]
  have hz (tree : UnaryActionTree) (q : Wire) (ancillas : List Wire) :
      tree.leafCostSum (fun label wire => ShorECDLP.tCount (tableXorGates wire (mask label))) q ancillas=0 := by
    induction tree generalizing q ancillas with
    | leaf label => simp [UnaryActionTree.leafCostSum]
    | node bit zero one ihz iho =>
      cases ancillas <;> simp only [UnaryActionTree.leafCostSum,ihz,iho,zero_add]
  rw [hz,zero_add]

theorem tableLookup_measurementCount (mask : Nat → List Wire) (tree : UnaryActionTree)
    (control : Wire) (ancillas : List Wire) (hl : tree.Layout control ancillas) :
    (tableLookup mask tree control ancillas).measurementCount=tree.internalNodes :=
  unaryAction_measurementCount _ _ _ _ _ hl

/-- A complete little-endian address decoder; base and stride carry its table index. -/
def tableAddressTree : List Wire → Nat → Nat → UnaryActionTree
  | [], base, _ => .leaf base
  | bit::bits, base, stride => .node bit
      (tableAddressTree bits base (2*stride))
      (tableAddressTree bits (base+stride) (2*stride))

theorem tableAddressTree_mem_index (bits : List Wire) (base stride : Nat) (w : Wire) :
    w∈(tableAddressTree bits base stride).indexWires ↔ w∈bits := by
  induction bits generalizing base stride with
  | nil => simp [tableAddressTree,UnaryActionTree.indexWires]
  | cons bit bits ih => simp [tableAddressTree,UnaryActionTree.indexWires,ih]

theorem tableAddressTree_index (bits : List Wire) (base stride : Nat) (hn : bits.Nodup) :
    (tableAddressTree bits base stride).indexWires.dedup=bits := by
  induction bits generalizing base stride with
  | nil => rfl
  | cons bit bits ih =>
    have hbit := (List.nodup_cons.mp hn).1
    have hs : (tableAddressTree bits base (2*stride)).indexWires ⊆
        (tableAddressTree bits (base+stride) (2*stride)).indexWires := by
      intro w hw
      exact (tableAddressTree_mem_index _ _ _ _).mpr ((tableAddressTree_mem_index _ _ _ _).mp hw)
    rw [tableAddressTree,UnaryActionTree.indexWires,List.dedup_cons_of_notMem]
    · rw [hs.dedup_append_right,ih _ _ (List.nodup_cons.mp hn).2]
    · simp only [List.mem_append,tableAddressTree_mem_index]
      exact fun h => h.elim hbit hbit

theorem tableAddressTree_nodes (bits : List Wire) (base stride : Nat) :
    (tableAddressTree bits base stride).internalNodes+1=2^bits.length := by
  induction bits generalizing base stride with
  | nil => rfl
  | cons bit bits ih =>
    simp only [tableAddressTree,UnaryActionTree.internalNodes,List.length_cons,pow_succ]
    have h0 := ih base (2*stride)
    have h1 := ih (base+stride) (2*stride)
    omega

theorem tableAddressTree_layout (bits ancillas : List Wire) (q : Wire) (base stride : Nat)
    (hlen : bits.length≤ancillas.length) (hn : (q::bits++ancillas).Nodup) :
    (tableAddressTree bits base stride).Layout q ancillas := by
  induction bits generalizing ancillas q base stride with
  | nil => exact UnaryActionTree.Layout.leaf base q ancillas (by simpa using hn)
  | cons bit bits ih =>
    cases ancillas with
    | nil => simp at hlen
    | cons path rest =>
      have hbits : (bit::bits).Nodup := ((List.nodup_cons.mp hn).2).of_append_left
      have hdrop : (bits ++ path::rest).Nodup :=
        (List.nodup_cons.mp (List.nodup_cons.mp hn).2).2
      have hchild : (path::bits++rest).Nodup := List.perm_middle.nodup_iff.mp hdrop
      apply UnaryActionTree.Layout.node bit q path _ _ rest
      · change (q :: (tableAddressTree (bit::bits) base stride).indexWires.dedup ++ path::rest).Nodup
        rw [tableAddressTree_index _ _ _ hbits]
        exact hn
      · exact ih rest path base (2*stride) (by simpa using hlen) hchild
      · exact ih rest path (base+stride) (2*stride) (by simpa using hlen) hchild

/-- Little-endian numeric value of the address bits. -/
def tableAddressValue : List Wire → BasisState → Nat
  | [], _ => 0
  | bit::bits, s => (s bit).toNat + 2 * tableAddressValue bits s

theorem tableAddressValue_lt (bits : List Wire) (s : BasisState) :
    tableAddressValue bits s < 2^bits.length := by
  induction bits with
  | nil => simp [tableAddressValue]
  | cons bit bits ih =>
    simp only [tableAddressValue,List.length_cons,pow_succ]
    cases s bit <;> simp only [Bool.toNat_false,Bool.toNat_true] <;> omega

theorem tableAddressTree_route (bits : List Wire) (base stride : Nat) (s : BasisState) :
    (tableAddressTree bits base stride).routeLabel s = base + stride * tableAddressValue bits s := by
  induction bits generalizing base stride with
  | nil => simp [tableAddressTree,UnaryActionTree.routeLabel,tableAddressValue]
  | cons bit bits ih =>
    cases h : s bit <;>
      simp [tableAddressTree,UnaryActionTree.routeLabel,tableAddressValue,h,ih] <;> ring

/-- The actual measured lookup for a complete address register. -/
def tableLookupProgram (mask : Nat → List Wire) (bits : List Wire) (control : Wire)
    (ancillas : List Wire) : AdaptiveCircuit :=
  tableLookup mask (tableAddressTree bits 0 1) control ancillas

theorem tableLookupProgram_tCount (mask : Nat → List Wire) (bits ancillas : List Wire)
    (q : Wire) (hlen : bits.length≤ancillas.length) (hn : (q::bits++ancillas).Nodup) :
    (tableLookupProgram mask bits q ancillas).tCount=7*(2^bits.length-1) := by
  rw [tableLookupProgram,tableLookup_tCount _ _ _ _ (tableAddressTree_layout _ _ _ _ _ hlen hn)]
  have h := tableAddressTree_nodes bits 0 1
  congr 1
  omega

theorem tableLookupProgram_measurementCount (mask : Nat → List Wire) (bits ancillas : List Wire)
    (q : Wire) (hlen : bits.length≤ancillas.length) (hn : (q::bits++ancillas).Nodup) :
    (tableLookupProgram mask bits q ancillas).measurementCount=2^bits.length-1 := by
  rw [tableLookupProgram,tableLookup_measurementCount _ _ _ _ (tableAddressTree_layout _ _ _ _ _ hlen hn)]
  have h := tableAddressTree_nodes bits 0 1
  omega

private theorem tableLookupUnitary_support (mask : Nat → List Wire) (tree : UnaryActionTree)
    (q : Wire) (ancillas support : List Wire) (hq : q∈support)
    (hi : tree.indexWires ⊆ support) (ha : ancillas ⊆ support)
    (hm : ∀ label, mask label ⊆ support) :
    PaperCircuitUsesOnly support (unaryActionUnitary .inc
      (fun label q => tableXorGates q (mask label)) tree q ancillas) := by
  induction tree generalizing q ancillas with
  | leaf label =>
    intro g hg w hw
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hg
    simp only [gateWires,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl
    · exact hq
    · exact hm label ht
  | node bit zero one hz ho =>
    cases ancillas with
    | nil => simp [unaryActionUnitary,PaperCircuitUsesOnly]
    | cons path rest =>
      have hb := hi (by simp [UnaryActionTree.indexWires] : bit∈(UnaryActionTree.node bit zero one).indexWires)
      have hp := ha (by simp : path∈path::rest)
      have hr : rest ⊆ support := by intro w hw; exact ha (by simp [hw])
      have hz' := hz path rest hp (by intro w hw; exact hi (by simp [UnaryActionTree.indexWires,hw])) hr
      have ho' := ho path rest hp (by intro w hw; exact hi (by simp [UnaryActionTree.indexWires,hw])) hr
      have hc : PaperCircuitUsesOnly support (computeZeroAnd q bit path) := by
        simp [computeZeroAnd,PaperCircuitUsesOnly,PaperGateUsesOnly,gateWires,hq,hb,hp]
      have ht : PaperCircuitUsesOnly support ([.CX q path] : Circuit) := by
        simp [PaperCircuitUsesOnly,PaperGateUsesOnly,gateWires,hq,hp]
      simpa only [unaryActionUnitary,List.nil_append,List.append_assoc] using
        hc.append (hz'.append (ht.append (ho'.append (ht.append hc))))

theorem tableLookupProgram_support (mask : Nat → List Wire) (bits ancillas targets : List Wire)
    (q : Wire) (hm : ∀ label, mask label ⊆ targets) :
    (tableLookupProgram mask bits q ancillas).wires ⊆ q::bits++ancillas++targets := by
  have hu := tableLookupUnitary_support mask (tableAddressTree bits 0 1) q ancillas
    (q::bits++ancillas++targets) (by simp)
    (by intro w hw; have h := (tableAddressTree_mem_index _ _ _ _).mp hw; simp [h])
    (by intro w hw; simp [hw]) (by intro label w hw; have h := hm label hw; simp [h])
  intro w hw
  have h := unaryAction_wires_subset .inc (fun label q => tableXorGates q (mask label))
    (tableAddressTree bits 0 1) q ancillas hw
  obtain ⟨g,hg,hw⟩ := List.mem_flatMap.mp h
  exact hu g hg w hw

theorem tableLookupProgram_qubitCount (mask : Nat → List Wire) (bits ancillas targets : List Wire)
    (q : Wire) (hm : ∀ label, mask label ⊆ targets) :
    (tableLookupProgram mask bits q ancillas).qubitCount ≤
      1+bits.length+ancillas.length+targets.length := by
  have hs : (tableLookupProgram mask bits q ancillas).wires.dedup.toFinset ⊆
      (q::bits++ancillas++targets).toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (tableLookupProgram_support mask bits ancillas targets q hm
      (by simpa using hw))
  have hc := (Finset.card_le_card hs).trans (List.toFinset_card_le _)
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _)] at hc
  simpa only [AdaptiveCircuit.qubitCount,List.length_append,List.length_cons,Nat.add_comm 1] using hc

theorem tableLookupProgram_run (mask : Nat → List Wire) (bits ancillas : List Wire)
    (q : Wire) (hlen : bits.length≤ancillas.length) (hn : (q::bits++ancillas).Nodup)
    (hm : ∀ label, (mask label).Nodup)
    (hd : ∀ label w, w∈q::bits++ancillas → w∉mask label)
    (s : BasisState) (hc : Clean ancillas s) :
    Classical.run (unaryActionUnitary .inc (fun label q => tableXorGates q (mask label))
      (tableAddressTree bits 0 1) q ancillas) s =
      tableXorState (mask (tableAddressValue bits s)) (s q) s := by
  have hb : bits.Nodup := (List.nodup_cons.mp hn).2.of_append_left
  simpa only [tableAddressTree_route,zero_add,one_mul] using
    tableLookup_run mask (tableAddressTree bits 0 1) q ancillas
      (tableAddressTree_layout _ _ _ _ _ hlen hn) hm
      (by simpa only [tableAddressTree_index _ _ _ hb] using hd) s hc

theorem tableAddressValue_preserved (bits : List Wire) (selected : List Wire)
    (active : Bool) (s : BasisState) (hd : ∀ w, w∈bits → w∉selected) :
    tableAddressValue bits (tableXorState selected active s)=tableAddressValue bits s := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    simp only [tableAddressValue,tableXorState_outside _ _ _ bit (hd bit (by simp)),
      ih (by intro w hw; exact hd w (by simp [hw]))]

/-- Repeating the same selected-entry operation clears the load and restores the whole state. -/
theorem tableLookupProgram_clear (mask : Nat → List Wire) (bits ancillas : List Wire)
    (q : Wire) (hlen : bits.length≤ancillas.length) (hn : (q::bits++ancillas).Nodup)
    (hm : ∀ label, (mask label).Nodup)
    (hd : ∀ label w, w∈q::bits++ancillas → w∉mask label)
    (s : BasisState) (hc : Clean ancillas s) :
    let circuit := unaryActionUnitary .inc (fun label q => tableXorGates q (mask label))
      (tableAddressTree bits 0 1) q ancillas
    Classical.run (circuit++circuit) s=s := by
  dsimp only
  rw [Classical.run_append,tableLookupProgram_run mask bits ancillas q hlen hn hm hd s hc]
  have hc' : Clean ancillas (tableXorState (mask (tableAddressValue bits s)) (s q) s) := by
    intro w hw
    rw [tableXorState_outside _ _ _ _ (hd _ w (by simp [hw]))]
    exact hc w hw
  rw [tableLookupProgram_run mask bits ancillas q hlen hn hm hd _ hc',
    tableAddressValue_preserved bits _ _ s (by intro w hw; exact hd _ w (by simp [hw])),
    tableXorState_outside _ _ _ q (hd _ q (by simp)),tableXorState_involution]

theorem tableLookupProgram_coherent (mask : Nat → List Wire) (bits ancillas : List Wire)
    (q : Wire) (hlen : bits.length≤ancillas.length) (hn : (q::bits++ancillas).Nodup)
    (hm : ∀ label, (mask label).Nodup)
    (hd : ∀ label w, w∈q::bits++ancillas → w∉mask label) :
    CoherentlyImplementsOn (tableLookupProgram mask bits q ancillas)
      (Quantum.run (unaryActionUnitary .inc (fun label q => tableXorGates q (mask label))
        (tableAddressTree bits 0 1) q ancillas)) (Clean ancillas) := by
  have hb : bits.Nodup := (List.nodup_cons.mp hn).2.of_append_left
  exact tableLookup_coherent mask _ q ancillas
    (tableAddressTree_layout _ _ _ _ _ hlen hn) hm
    (by simpa only [tableAddressTree_index _ _ _ hb] using hd)

theorem tableLookupProgram_wellFormed (mask : Nat → List Wire) (bits ancillas : List Wire)
    (q : Wire) (hlen : bits.length≤ancillas.length) (hn : (q::bits++ancillas).Nodup)
    (hd : ∀ label w, w∈q::bits++ancillas → w∉mask label) :
    (tableLookupProgram mask bits q ancillas).WellFormed := by
  have hb : bits.Nodup := (List.nodup_cons.mp hn).2.of_append_left
  exact tableLookup_wellFormed mask _ q ancillas
    (tableAddressTree_layout _ _ _ _ _ hlen hn)
    (by simpa only [tableAddressTree_index _ _ _ hb] using hd)

/-- The actual adaptive load followed by the same lookup is coherently the identity. -/
theorem tableLookupProgram_coherent_clear (mask : Nat → List Wire) (bits ancillas : List Wire)
    (q : Wire) (hlen : bits.length≤ancillas.length) (hn : (q::bits++ancillas).Nodup)
    (hm : ∀ label, (mask label).Nodup)
    (hd : ∀ label w, w∈q::bits++ancillas → w∉mask label) :
    CoherentlyImplementsOn
      ((tableLookupProgram mask bits q ancillas).seq (tableLookupProgram mask bits q ancillas))
      (LinearMap.id : Quantum.State →ₗ[ℂ] Quantum.State) (Clean ancillas) := by
  let reference := unaryActionUnitary .inc (fun label q => tableXorGates q (mask label))
    (tableAddressTree bits 0 1) q ancillas
  have hfree : HPFree reference := unaryActionUnitary_HPFree _ _ _ _ _
    (by intro label control; exact tableXorGates_HPFree control _)
  have hlookup := tableLookupProgram_coherent mask bits ancillas q hlen hn hm hd
  apply (hlookup.seq hlookup ?_).congrIdeal
  · intro s hs
    change Quantum.run reference (Quantum.run reference (ket s))=ket s
    rw [← Quantum.run_append,run_ket_agrees_classical _ _ (by simp [hfree])]
    rw [tableLookupProgram_clear mask bits ancillas q hlen hn hm hd s hs]
  · intro s hs
    rw [run_ket_agrees_classical _ _ hfree,
      tableLookupProgram_run mask bits ancillas q hlen hn hm hd s hs]
    apply supportedOn_ket
    intro w hw
    rw [tableXorState_outside _ _ _ _ (hd _ w (by simp [hw]))]
    exact hs w hw

/-- Readable resource certificate for one 16-bit-address, 256-bit-output lookup.
The 16 path wires are reusable after every lookup. -/
theorem tableLookupProgram_16_256_resources
    (mask : Nat → List Wire) (bits ancillas targets : List Wire) (q : Wire)
    (hb : bits.length=16) (ha : ancillas.length=16) (ht : targets.length=256)
    (hn : (q::bits++ancillas).Nodup) (hm : ∀ label, mask label ⊆ targets) :
    (tableLookupProgram mask bits q ancillas).tCount=458745 ∧
    (tableLookupProgram mask bits q ancillas).measurementCount=65535 ∧
    (tableLookupProgram mask bits q ancillas).qubitCount≤289 := by
  have hl : bits.length≤ancillas.length := by omega
  constructor
  · rw [tableLookupProgram_tCount _ _ _ _ hl hn,hb]
    decide
  constructor
  · rw [tableLookupProgram_measurementCount _ _ _ _ hl hn,hb]
    decide
  · simpa only [hb,ha,ht] using tableLookupProgram_qubitCount mask bits ancillas targets q hm

end
end ShorECDLP.Paper2607_13816
