import ShorECDLP.Submission.«2607_13816».Window.TableLookup
import ShorECDLP.Submission.«2607_13816».Arithmetic.SquareCoherent
/-!
# Lookup-loaded modular arithmetic

The actual measured QROM loads a canonical field word into one clean register,
which the existing modular adder can borrow internally and restore. A second
lookup clears the word. Coherent composition and the complete-state theorem
prove numeric addition with all non-accumulator wires restored.
-/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section
/-- Both variable operands are canonical and the four arithmetic helpers are clean. -/
def VariableModularValid (input acc : List Wire) (p : Nat) (c r t f : Wire) (s : BasisState) : Prop :=
  s c=false ∧ s r=false ∧ s t=false ∧ s f=false ∧
    boolWordToNat (wireValues input s)<p ∧ boolWordToNat (wireValues acc s)<p

private theorem variableModular_zero_valid (input acc : List Wire) (p : Nat) (c r t f : Wire)
    (hp : 0<p) : VariableModularValid input acc p c r t f (fun _ => false) := by
  have hz (ws : List Wire) : boolWordToNat (wireValues ws (fun _ => false))=0 := by
    induction ws with
    | nil => rfl
    | cons w ws ih => simpa [wireValues,boolWordToNat] using ih
  exact ⟨rfl,rfl,rfl,rfl,by rw [hz]; exact hp,by rw [hz]; exact hp⟩

theorem controlledModularAdd_coherent (input acc : List Wire) (correction : List Bool)
    (p : Nat) (q c r t f : Wire) (hlen : input.length=acc.length) (hne : 0<acc.length)
    (hk : acc.length=correction.length) (hnd : ([q,c,r,t,f]++input++acc).Nodup)
    (hp0 : 0<p) (hp : p<2^acc.length)
    (hconstant : boolWordToNat correction=2^acc.length-p) :
    CoherentlyImplementsOn (controlledModularAdd input acc correction p q c r t f)
      (Finsupp.lmapDomain ℂ ℂ (modularAddIdealState input acc correction p q c f))
      (VariableModularValid input acc p c r t f) := by
  apply coherent_history_branches _ _ _
    (controlledModularAdd_wellFormed input acc correction p q c r t f hlen hne hk hnd)
    (fun _ => false) (variableModular_zero_valid input acc p c r t f hp0)
  intro b hb s hs
  have h := controlledModularAdd_branch_correct input acc correction p q c r t f s
    hlen hne hk hnd hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hp hs.2.2.2.2.1 hs.2.2.2.2.2 hconstant b hb
  rw [h.1]
  exact h.2


/-- The selected one-bit positions of a table word. -/
def tableBitsMask : List Wire → List Bool → List Wire
  | w::ws, b::bs => if b then w::tableBitsMask ws bs else tableBitsMask ws bs
  | _, _ => []

theorem tableBitsMask_subset (targets : List Wire) (bits : List Bool) :
    tableBitsMask targets bits ⊆ targets := by
  induction targets generalizing bits with
  | nil => simp [tableBitsMask]
  | cons w ws ih =>
    cases bits with
    | nil => simp [tableBitsMask]
    | cons b bs =>
      cases b <;> simp only [tableBitsMask,Bool.false_eq_true,if_false,if_true]
      · exact (ih bs).trans (by intro v hv; simp [hv])
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · simp
        · exact List.mem_cons_of_mem _ (ih bs hv)

theorem tableBitsMask_nodup (targets : List Wire) (bits : List Bool) (hn : targets.Nodup) :
    (tableBitsMask targets bits).Nodup := by
  induction targets generalizing bits with
  | nil => simp [tableBitsMask]
  | cons w ws ih =>
    cases bits with
    | nil => simp [tableBitsMask]
    | cons b bs =>
      cases b <;> simp only [tableBitsMask,Bool.false_eq_true,if_false,if_true]
      · exact ih bs (List.nodup_cons.mp hn).2
      · exact List.nodup_cons.mpr ⟨fun h => (List.nodup_cons.mp hn).1
          (tableBitsMask_subset ws bs h),ih bs (List.nodup_cons.mp hn).2⟩

def tableWordMask (targets : List Wire) (value : Nat) : List Wire :=
  tableBitsMask targets (constantBits targets.length value)

theorem tableBitsMask_read (targets : List Wire) (bits : List Bool) (s : BasisState)
    (hn : targets.Nodup) (hl : targets.length=bits.length) (hc : Clean targets s) :
    wireValues targets (tableXorState (tableBitsMask targets bits) true s)=bits := by
  induction targets generalizing bits with
  | nil => cases bits <;> simp_all [wireValues]
  | cons w ws ih =>
    cases bits with
    | nil => simp at hl
    | cons b bs =>
      have hw := hc w (by simp)
      have ht : Clean ws s := by intro v hv; exact hc v (by simp [hv])
      have hwm : w∉tableBitsMask ws bs := fun h =>
        (List.nodup_cons.mp hn).1 (tableBitsMask_subset ws bs h)
      have he : wireValues ws (tableXorState (w::tableBitsMask ws bs) true s)=
          wireValues ws (tableXorState (tableBitsMask ws bs) true s) := by
        apply List.map_congr_left
        intro v hv
        have hne : v≠w := by intro h; subst v; exact (List.nodup_cons.mp hn).1 hv
        simp [tableXorState,hne]
      cases b <;> simp only [tableBitsMask,Bool.false_eq_true,if_false,if_true,wireValues,List.map_cons]
      · rw [show tableXorState (tableBitsMask ws bs) true s w=false by simp [tableXorState,hw,hwm]]
        congr 1
        exact ih bs (List.nodup_cons.mp hn).2 (by simpa using hl) ht
      · rw [show tableXorState (w::tableBitsMask ws bs) true s w=true by simp [tableXorState,hw]]
        congr 1
        rw [show List.map (tableXorState (w::tableBitsMask ws bs) true s) ws =
          wireValues ws (tableXorState (w::tableBitsMask ws bs) true s) from rfl,he]
        exact ih bs (List.nodup_cons.mp hn).2 (by simpa using hl) ht

theorem tableWordMask_read (targets : List Wire) (value : Nat) (s : BasisState)
    (hn : targets.Nodup) (hc : Clean targets s) :
    boolWordToNat (wireValues targets (tableXorState (tableWordMask targets value) true s))=
      value%2^targets.length := by
  rw [tableWordMask,tableBitsMask_read targets _ s hn (constantBits_length _ _).symm hc,
    boolWordToNat_constantBits]

/-- Whole-state map for a lookup, including an arbitrary root control. -/
def tableLookupState (mask : Nat → List Wire) (bits : List Wire) (q : Wire)
    (s : BasisState) : BasisState :=
  tableXorState (mask (tableAddressValue bits s)) (s q) s

theorem tableLookupProgram_coherent_state (mask : Nat → List Wire) (bits ancillas : List Wire)
    (q : Wire) (hlen : bits.length≤ancillas.length) (hn : (q::bits++ancillas).Nodup)
    (hm : ∀ label, (mask label).Nodup)
    (hd : ∀ label w, w∈q::bits++ancillas → w∉mask label) :
    CoherentlyImplementsOn (tableLookupProgram mask bits q ancillas)
      (Finsupp.lmapDomain ℂ ℂ (tableLookupState mask bits q)) (Clean ancillas) := by
  apply (tableLookupProgram_coherent mask bits ancillas q hlen hn hm hd).congrIdeal
  intro s hs
  rw [run_ket_agrees_classical _ _ (unaryActionUnitary_HPFree _ _ _ _ _
    (by intro label control; exact tableXorGates_HPFree control _)),
    tableLookupProgram_run mask bits ancillas q hlen hn hm hd s hs]
  simp [tableLookupState,ket]

/-- One field word is loaded, used by actual modular addition, then cleared. -/
def lookupModularAddProgram (table : Nat → Nat) (bits ancillas input acc : List Wire)
    (correction : List Bool) (p : Nat) (q c r t f : Wire) : AdaptiveCircuit :=
  ((tableLookupProgram (fun label => tableWordMask input (table label)) bits q ancillas).seq
    (controlledModularAdd input acc correction p q c r t f)).seq
    (tableLookupProgram (fun label => tableWordMask input (table label)) bits q ancillas)

def lookupModularAddState (table : Nat → Nat) (bits input acc : List Wire)
    (correction : List Bool) (p : Nat) (q c f : Wire) (s : BasisState) : BasisState :=
  let load := tableLookupState (fun label => tableWordMask input (table label)) bits q
  load (modularAddIdealState input acc correction p q c f (load s))

/-- The lookup word and path are clean, its root is enabled, and arithmetic is ready. -/
def LookupModularValid (ancillas input acc : List Wire) (p : Nat) (q c r t f : Wire)
    (s : BasisState) : Prop :=
  Clean ancillas s ∧ Clean input s ∧ s q=true ∧ s c=false ∧ s r=false ∧
    s t=false ∧ s f=false ∧ boolWordToNat (wireValues acc s)<p

private theorem lookupLoaded_valid (table : Nat → Nat) (bits ancillas input acc : List Wire)
    (p : Nat) (q c r t f : Wire) (hnd : ([q,c,r,t,f]++input++acc).Nodup)
    (hp : p<2^input.length) (hv : ∀ label, table label<p)
    (s : BasisState) (hs : LookupModularValid ancillas input acc p q c r t f s) :
    VariableModularValid input acc p c r t f
      (tableLookupState (fun label => tableWordMask input (table label)) bits q s) := by
  have hi : input.Nodup := hnd.of_append_left.of_append_right
  have hsep := List.disjoint_of_nodup_append hnd
  have hhelpers := List.disjoint_of_nodup_append hnd.of_append_left
  have hout (w : Wire) (hw : w∉input) :
      tableLookupState (fun label => tableWordMask input (table label)) bits q s w=s w := by
    apply tableXorState_outside
    exact fun h => hw (tableBitsMask_subset _ _ h)
  have hh (w : Wire) (hw : w∈[q,c,r,t,f]) : w∉input := List.disjoint_left.mp hhelpers hw
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [hout c (hh c (by simp))]; exact hs.2.2.2.1
  · rw [hout r (hh r (by simp))]; exact hs.2.2.2.2.1
  · rw [hout t (hh t (by simp))]; exact hs.2.2.2.2.2.1
  · rw [hout f (hh f (by simp))]; exact hs.2.2.2.2.2.2.1
  · unfold tableLookupState
    rw [hs.2.2.1,tableWordMask_read input _ s hi hs.2.1,Nat.mod_eq_of_lt ((hv _).trans hp)]
    exact hv _
  · have he : wireValues acc (tableLookupState (fun label => tableWordMask input (table label)) bits q s)=wireValues acc s := by
      apply List.map_congr_left
      intro w hw
      apply hout
      intro hiw
      exact List.disjoint_left.mp hsep (by simp [hiw]) hw
    rw [he]
    exact hs.2.2.2.2.2.2.2

private theorem lookup_coherent_strengthen {program : AdaptiveCircuit}
    {ideal : Quantum.State →ₗ[ℂ] Quantum.State} {Valid Stronger : BasisState → Prop}
    (h : CoherentlyImplementsOn program ideal Valid) (hsub : ∀ s, Stronger s → Valid s) :
    CoherentlyImplementsOn program ideal Stronger := by
  obtain ⟨cs,ha,hm⟩ := h
  exact ⟨cs,ha.imp (fun b c hb s hs => hb s (hsub s hs)),hm⟩

theorem lookupModularAddProgram_coherent (table : Nat → Nat) (bits ancillas input acc : List Wire)
    (correction : List Bool) (p : Nat) (q c r t f : Wire)
    (hl : bits.length≤ancillas.length) (hn : (q::bits++ancillas).Nodup)
    (hd : (q::bits++ancillas).Disjoint input) (ha : ancillas.Disjoint acc)
    (hlen : input.length=acc.length) (hne : 0<acc.length)
    (hk : acc.length=correction.length) (hnd : ([q,c,r,t,f]++input++acc).Nodup)
    (hp0 : 0<p) (hp : p<2^acc.length) (hconstant : boolWordToNat correction=2^acc.length-p)
    (hv : ∀ label, table label<p) :
    CoherentlyImplementsOn (lookupModularAddProgram table bits ancillas input acc correction p q c r t f)
      (Finsupp.lmapDomain ℂ ℂ (lookupModularAddState table bits input acc correction p q c f))
      (LookupModularValid ancillas input acc p q c r t f) := by
  let load := tableLookupState (fun label => tableWordMask input (table label)) bits q
  have hm (label : Nat) : (tableWordMask input (table label)).Nodup :=
    tableBitsMask_nodup _ _ hnd.of_append_left.of_append_right
  have hmask (label w : Nat) (hw : w∈q::bits++ancillas) : w∉tableWordMask input (table label) :=
    fun h => List.disjoint_left.mp hd hw (tableBitsMask_subset _ _ h)
  have hlookup := tableLookupProgram_coherent_state (fun label => tableWordMask input (table label)) bits ancillas q hl hn hm hmask
  have hfirst : CoherentlyImplementsOn
      (tableLookupProgram (fun label => tableWordMask input (table label)) bits q ancillas)
      (Finsupp.lmapDomain ℂ ℂ load) (LookupModularValid ancillas input acc p q c r t f) :=
    lookup_coherent_strengthen hlookup (fun _ hs => hs.1)
  have hbody := controlledModularAdd_coherent input acc correction p q c r t f hlen hne hk hnd hp0 hp hconstant
  have hpair := hfirst.seq hbody (by
    intro s hs
    have h := lookupLoaded_valid table bits ancillas input acc p q c r t f hnd (by simpa only [hlen] using hp) hv s hs
    simpa [ket] using supportedOn_ket (VariableModularValid input acc p c r t f) (load s) h)
  apply (hpair.seq hlookup ?_).congrIdeal
  · intro s hs
    simp [lookupModularAddState,load,LinearMap.comp_apply,ket]
  · intro s hs
    have hv' := lookupLoaded_valid table bits ancillas input acc p q c r t f hnd (by simpa only [hlen] using hp) hv s hs
    have hf := (modularAddIdealState_correct input acc correction p q c r t f (load s)
      hlen hk hnd hv'.1 hv'.2.2.2.1 hp hv'.2.2.2.2.1 hv'.2.2.2.2.2 hconstant).2
    have hclean : Clean ancillas (modularAddIdealState input acc correction p q c f (load s)) := by
      intro w hw
      rw [hf w (List.disjoint_left.mp ha hw)]
      change tableXorState _ _ s w=false
      rw [tableXorState_outside _ _ _ w (hmask _ w (by simp [hw]))]
      exact hs.1 w hw
    simpa [LinearMap.comp_apply,ket] using supportedOn_ket (Clean ancillas) _ hclean

theorem tableAddressValue_congr (bits : List Wire) (s t : BasisState)
    (h : ∀ w, w∈bits → s w=t w) : tableAddressValue bits s=tableAddressValue bits t := by
  induction bits with
  | nil => rfl
  | cons w ws ih =>
    simp only [tableAddressValue,h w (by simp),ih (by intro v hv; exact h v (by simp [hv]))]

/-- Numeric addition and complete restoration outside the accumulator, including the lookup word. -/
theorem lookupModularAddState_correct (table : Nat → Nat) (bits ancillas input acc : List Wire)
    (correction : List Bool) (p : Nat) (q c r t f : Wire)
    (hd : (q::bits++ancillas).Disjoint input) (hb : bits.Disjoint acc)
    (hlen : input.length=acc.length) (hk : acc.length=correction.length)
    (hnd : ([q,c,r,t,f]++input++acc).Nodup) (hp : p<2^acc.length)
    (hconstant : boolWordToNat correction=2^acc.length-p) (hv : ∀ label, table label<p)
    (s : BasisState) (hs : LookupModularValid ancillas input acc p q c r t f s) :
    boolWordToNat (wireValues acc (lookupModularAddState table bits input acc correction p q c f s))=
      (boolWordToNat (wireValues acc s)+table (tableAddressValue bits s))%p ∧
    (∀ w, w∉acc → lookupModularAddState table bits input acc correction p q c f s w=s w) := by
  let mask := fun label => tableWordMask input (table label)
  let loaded := tableLookupState mask bits q s
  let after := modularAddIdealState input acc correction p q c f loaded
  have hvalid := lookupLoaded_valid table bits ancillas input acc p q c r t f hnd
    (by simpa only [hlen] using hp) hv s hs
  have hbody := modularAddIdealState_correct input acc correction p q c r t f loaded
    hlen hk hnd hvalid.1 hvalid.2.2.2.1 hp hvalid.2.2.2.2.1 hvalid.2.2.2.2.2 hconstant
  have hsep := List.disjoint_of_nodup_append hnd
  have hiacc : input.Disjoint acc := by
    apply List.disjoint_left.mpr
    intro w hw
    exact List.disjoint_left.mp hsep (by simp [hw])
  have hload (w : Wire) (hw : w∉input) : loaded w=s w :=
    tableXorState_outside _ _ _ _ (fun h => hw (tableBitsMask_subset _ _ h))
  have hqinput : q∉input := List.disjoint_left.mp hd (by simp)
  have hqacc : q∉acc := List.disjoint_left.mp hsep (by simp)
  have hqload : loaded q=true := (hload q hqinput).trans hs.2.2.1
  have hqafter : after q=true := (hbody.2 q hqacc).trans hqload
  have haddress : tableAddressValue bits after=tableAddressValue bits s := by
    apply tableAddressValue_congr
    intro w hw
    exact (hbody.2 w (List.disjoint_left.mp hb hw)).trans
      (hload w (List.disjoint_left.mp hd (by simp [hw])))
  have hfinal : lookupModularAddState table bits input acc correction p q c f s=
      tableXorState (mask (tableAddressValue bits s)) true after := by
    change tableXorState (mask (tableAddressValue bits after)) (after q) after = _
    rw [haddress,hqafter]
  have haccload : wireValues acc loaded=wireValues acc s := by
    apply List.map_congr_left
    intro w hw
    exact hload w (fun h => List.disjoint_left.mp hiacc h hw)
  have hinput : boolWordToNat (wireValues input loaded)=table (tableAddressValue bits s) := by
    change boolWordToNat (wireValues input (tableXorState _ (s q) s))=_
    rw [hs.2.2.1,tableWordMask_read input _ s hnd.of_append_left.of_append_right hs.2.1,
      Nat.mod_eq_of_lt ((hv _).trans (by simpa only [hlen] using hp))]
  constructor
  · have hacc : wireValues acc (lookupModularAddState table bits input acc correction p q c f s)=wireValues acc after := by
      rw [hfinal]
      apply List.map_congr_left
      intro w hw
      exact tableXorState_outside _ _ _ w
        (fun h => List.disjoint_left.mp hiacc (tableBitsMask_subset _ _ h) hw)
    rw [hacc]
    simpa only [hqload,if_true,haccload,hinput] using hbody.1
  · intro w hw
    rw [hfinal]
    have hafter : after w=loaded w := hbody.2 w hw
    simp only [tableXorState,hafter,loaded,tableLookupState,hs.2.2.1]
    simp

/-- Exact lookup overhead around the unchanged variable modular-adder body. -/
theorem lookupModularAddProgram_resources (table : Nat → Nat) (bits ancillas input acc : List Wire)
    (correction : List Bool) (p : Nat) (q c r t f : Wire)
    (hl : bits.length≤ancillas.length) (hn : (q::bits++ancillas).Nodup) :
    (lookupModularAddProgram table bits ancillas input acc correction p q c r t f).tCount=
      (controlledModularAdd input acc correction p q c r t f).tCount+14*(2^bits.length-1) ∧
    (lookupModularAddProgram table bits ancillas input acc correction p q c r t f).measurementCount=
      (controlledModularAdd input acc correction p q c r t f).measurementCount+2*(2^bits.length-1) := by
  have hseq (a b : AdaptiveCircuit) : (a.seq b).tCount=a.tCount+b.tCount := by
    simpa only [gidneyGateCount_tCount] using modularGateCount_seq tCost a b
  constructor
  · rw [lookupModularAddProgram,hseq,hseq,tableLookupProgram_tCount _ _ _ _ hl hn]
    omega
  · rw [lookupModularAddProgram,modularMeasurements_seq,modularMeasurements_seq,
      tableLookupProgram_measurementCount _ _ _ _ hl hn]
    omega

end
end ShorECDLP.Paper2607_13816
