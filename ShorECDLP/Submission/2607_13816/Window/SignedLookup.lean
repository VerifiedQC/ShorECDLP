import ShorECDLP.Submission.«2607_13816».Window.NegativeControl
import ShorECDLP.Submission.«2607_13816».Window.LookupArithmetic
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section

def signedLookupModularAddProgram (table : Nat → Nat) (bits paths input acc : List Wire)
    (correction : List Bool) (p : Nat) (q sign c r t f : Wire) : AdaptiveCircuit :=
  let negate := negativeControlledModularNegate acc input (constantBits acc.length p) sign c r t f
  (negate.seq (lookupModularAddProgram table bits paths input acc correction p q c r t f)).seq negate

def signedLookupModularAddState (table : Nat → Nat) (bits input acc : List Wire)
    (correction : List Bool) (p : Nat) (q sign c f : Wire) (s : BasisState) : BasisState :=
  let negate := negativeModularNegateState acc (constantBits acc.length p) sign f
  negate (lookupModularAddState table bits input acc correction p q c f (negate s))

private theorem lookup_valid_update (paths input acc : List Wire) (p : Nat) (q c r t f : Wire)
    (hn : ([q,c,r,t,f]++input++acc).Nodup) (hd : paths.Disjoint acc)
    (s after : BasisState) (hs : LookupModularValid paths input acc p q c r t f s)
    (hf : ∀ w, w∉acc → after w=s w) (hv : boolWordToNat (wireValues acc after)<p) :
    LookupModularValid paths input acc p q c r t f after := by
  have he := List.disjoint_of_nodup_append hn
  have hsep (w : Wire) (hw : w∈[q,c,r,t,f]) : w∉acc :=
    List.disjoint_left.mp he (List.mem_append_left _ hw)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,hv⟩
  · intro w hw; rw [hf w (List.disjoint_left.mp hd hw)]; exact hs.1 w hw
  · intro w hw; rw [hf w (List.disjoint_left.mp he (List.mem_append_right _ hw))]; exact hs.2.1 w hw
  · exact (hf q (hsep q (by simp))).trans hs.2.2.1
  · exact (hf c (hsep c (by simp))).trans hs.2.2.2.1
  · exact (hf r (hsep r (by simp))).trans hs.2.2.2.2.1
  · exact (hf t (hsep t (by simp))).trans hs.2.2.2.2.2.1
  · exact (hf f (hsep f (by simp))).trans hs.2.2.2.2.2.2.1

private theorem lookup_negate_correct (paths input acc : List Wire) (p : Nat) (q sign c r t f : Wire)
    (hn : ([sign,c,r,t,f]++acc++input).Nodup) (hne : 0<acc.length) (hp : p<2^acc.length)
    (s : BasisState) (hs : LookupModularValid paths input acc p q c r t f s) :
    boolWordToNat (wireValues acc (negativeModularNegateState acc (constantBits acc.length p) sign f s))=
      (if s sign then boolWordToNat (wireValues acc s) else (p-boolWordToNat (wireValues acc s))%p) ∧
    ∀ w, w∉acc → negativeModularNegateState acc (constantBits acc.length p) sign f s w=s w := by
  have ha : acc.Nodup := hn.of_append_left.of_append_right
  have he := List.disjoint_of_nodup_append hn.of_append_left
  have hsacc : sign∉acc := List.disjoint_left.mp he (by simp)
  have hfacc : f∉acc := List.disjoint_left.mp he (by simp)
  have hsf : sign≠f := by
    have h := (List.nodup_cons.mp hn).1
    change sign∉([c,r,t,f]++acc++input) at h
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or] at h
    exact h.1.1.2.2.2
  exact negativeModularNegateState_correct acc (constantBits acc.length p) p sign f s hne (by simp) ha hsacc hfacc hsf
    hs.2.2.2.2.2.2.1 hp hs.2.2.2.2.2.2.2 (by rw [boolWordToNat_constantBits,Nat.mod_eq_of_lt hp])

private theorem signed_lookup_restrict {program : AdaptiveCircuit} {ideal : Quantum.State →ₗ[ℂ] Quantum.State}
    {P Q : BasisState → Prop} (h : CoherentlyImplementsOn program ideal P) (hq : ∀ s, Q s → P s) :
    CoherentlyImplementsOn program ideal Q := by
  obtain ⟨cs,hc,hm⟩ := h
  exact ⟨cs,hc.imp (fun b c hb s hs => hb s (hq s hs)),hm⟩

theorem signedLookupModularAddProgram_coherent (table : Nat → Nat) (bits paths input acc : List Wire)
    (correction : List Bool) (p : Nat) (q sign c r t f : Wire)
    (hl : bits.length≤paths.length) (hn : (q::bits++paths).Nodup)
    (hd : (q::bits++paths).Disjoint input) (ha : paths.Disjoint acc) (hb : bits.Disjoint acc)
    (hlen : input.length=acc.length) (hne : 0<acc.length) (hk : acc.length=correction.length)
    (hnd : ([q,c,r,t,f]++input++acc).Nodup) (hneg : ([sign,c,r,t,f]++acc++input).Nodup)
    (hp0 : 0<p) (hp : p<2^acc.length) (hconstant : boolWordToNat correction=2^acc.length-p)
    (hv : ∀ label, table label<p) :
    CoherentlyImplementsOn (signedLookupModularAddProgram table bits paths input acc correction p q sign c r t f)
      (Finsupp.lmapDomain ℂ ℂ (signedLookupModularAddState table bits input acc correction p q sign c f))
      (LookupModularValid paths input acc p q c r t f) := by
  let Valid := LookupModularValid paths input acc p q c r t f
  let neg := negativeModularNegateState acc (constantBits acc.length p) sign f
  let add := lookupModularAddState table bits input acc correction p q c f
  have rn (s : BasisState) (hs : Valid s) : Valid (neg s) := by
    have h := lookup_negate_correct paths input acc p q sign c r t f hneg hne hp s hs
    apply lookup_valid_update paths input acc p q c r t f hnd ha s (neg s) hs h.2
    rw [h.1]; split
    · exact hs.2.2.2.2.2.2.2
    · exact Nat.mod_lt _ hp0
  have ra (s : BasisState) (hs : Valid s) : Valid (add s) := by
    have h := lookupModularAddState_correct table bits paths input acc correction p q c r t f hd hb hlen hk hnd hp hconstant hv s hs
    apply lookup_valid_update paths input acc p q c r t f hnd ha s (add s) hs h.2
    rw [h.1]; exact Nat.mod_lt _ hp0
  have cn := signed_lookup_restrict
    (negativeControlledModularNegate_coherent acc input (constantBits acc.length p) p sign c r t f
      (by simp) hlen.symm hne hneg hp0) (Q:=Valid) (by
        intro s hs
        exact ⟨hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,hs.2.2.2.2.2.2.1,hs.2.2.2.2.2.2.2⟩)
  have ca := lookupModularAddProgram_coherent table bits paths input acc correction p q c r t f hl hn hd ha hlen hne hk hnd hp0 hp hconstant hv
  have first := cn.seq ca (by intro s hs; simpa [ket] using supportedOn_ket Valid (neg s) (rn s hs))
  have all := first.seq cn (by
    intro s hs
    simpa [LinearMap.comp_apply,ket] using supportedOn_ket Valid (add (neg s)) (ra _ (rn s hs)))
  apply all.congrIdeal
  intro s hs
  simp [signedLookupModularAddState,LinearMap.comp_apply,ket]
private theorem negate_add_negate (p y v : Nat) (hy : y<p) (hv : v<p) :
    (p-((p-y)%p+v)%p)%p=(y+p-v)%p := by
  by_cases hz : y=0
  · subst y
    simp [Nat.mod_eq_of_lt hv]
  · rw [Nat.mod_eq_of_lt (show p-y<p by omega)]
    by_cases hvy : v<y
    · rw [Nat.mod_eq_of_lt (show p-y+v<p by omega),show p-(p-y+v)=y-v by omega,
        show y+p-v=p+(y-v) by omega,Nat.add_mod,Nat.mod_self,Nat.zero_add,Nat.mod_mod]
    · rw [show p-y+v=p+(v-y) by omega,Nat.add_mod,Nat.mod_self,Nat.zero_add,Nat.mod_mod,
        Nat.mod_eq_of_lt (show v-y<p by omega),show p-(v-y)=y+p-v by omega]

theorem signedLookupModularAddState_correct (table : Nat → Nat) (bits paths input acc : List Wire)
    (correction : List Bool) (p : Nat) (q sign c r t f : Wire)
    (hd : (q::bits++paths).Disjoint input) (ha : paths.Disjoint acc) (hb : bits.Disjoint acc)
    (hlen : input.length=acc.length) (hne : 0<acc.length) (hk : acc.length=correction.length)
    (hnd : ([q,c,r,t,f]++input++acc).Nodup) (hneg : ([sign,c,r,t,f]++acc++input).Nodup)
    (hp0 : 0<p) (hp : p<2^acc.length) (hconstant : boolWordToNat correction=2^acc.length-p)
    (hv : ∀ label, table label<p) (s : BasisState) (hs : LookupModularValid paths input acc p q c r t f s) :
    boolWordToNat (wireValues acc (signedLookupModularAddState table bits input acc correction p q sign c f s))=
      (if s sign then (boolWordToNat (wireValues acc s)+table (tableAddressValue bits s))%p
       else (boolWordToNat (wireValues acc s)+p-table (tableAddressValue bits s))%p) ∧
    ∀ w, w∉acc → signedLookupModularAddState table bits input acc correction p q sign c f s w=s w := by
  let s1 := negativeModularNegateState acc (constantBits acc.length p) sign f s
  let s2 := lookupModularAddState table bits input acc correction p q c f s1
  have h1 := lookup_negate_correct paths input acc p q sign c r t f hneg hne hp s hs
  have v1 : LookupModularValid paths input acc p q c r t f s1 := by
    apply lookup_valid_update paths input acc p q c r t f hnd ha s s1 hs h1.2
    rw [h1.1]; split
    · exact hs.2.2.2.2.2.2.2
    · exact Nat.mod_lt _ hp0
  have h2 := lookupModularAddState_correct table bits paths input acc correction p q c r t f hd hb hlen hk hnd hp hconstant hv s1 v1
  have v2 : LookupModularValid paths input acc p q c r t f s2 := by
    apply lookup_valid_update paths input acc p q c r t f hnd ha s1 s2 v1 h2.2
    rw [h2.1]; exact Nat.mod_lt _ hp0
  have h3 := lookup_negate_correct paths input acc p q sign c r t f hneg hne hp s2 v2
  have hsign : sign∉acc := List.disjoint_left.mp (List.disjoint_of_nodup_append hneg.of_append_left) (by simp)
  have haddr : tableAddressValue bits s1=tableAddressValue bits s :=
    tableAddressValue_congr bits s1 s (fun w hw => h1.2 w (List.disjoint_left.mp hb hw))
  constructor
  · change boolWordToNat (wireValues acc (negativeModularNegateState acc (constantBits acc.length p) sign f s2))=_
    rw [h3.1]
    dsimp only [s2]
    rw [h2.2 sign hsign,h2.1,haddr]
    dsimp only [s1]
    rw [h1.2 sign hsign,h1.1]
    cases hsg : s sign
    · simp only [Bool.false_eq_true,if_false]
      exact negate_add_negate p _ _ hs.2.2.2.2.2.2.2 (hv _)
    · simp
  · intro w hw
    exact (h3.2 w hw).trans ((h2.2 w hw).trans (h1.2 w hw))

theorem signedLookupModularAddProgram_resources (table : Nat → Nat) (bits paths input acc : List Wire)
    (correction : List Bool) (p : Nat) (q sign c r t f : Wire)
    (hl : bits.length≤paths.length) (hn : (q::bits++paths).Nodup) :
    (signedLookupModularAddProgram table bits paths input acc correction p q sign c r t f).tCount=
      2*(negativeControlledModularNegate acc input (constantBits acc.length p) sign c r t f).tCount+
      (controlledModularAdd input acc correction p q c r t f).tCount+14*(2^bits.length-1) ∧
    (signedLookupModularAddProgram table bits paths input acc correction p q sign c r t f).measurementCount=
      2*(negativeControlledModularNegate acc input (constantBits acc.length p) sign c r t f).measurementCount+
      (controlledModularAdd input acc correction p q c r t f).measurementCount+2*(2^bits.length-1) := by
  have h := lookupModularAddProgram_resources table bits paths input acc correction p q c r t f hl hn
  have ht (a b : AdaptiveCircuit) : (a.seq b).tCount=a.tCount+b.tCount := by
    simpa only [gidneyGateCount_tCount] using modularGateCount_seq tCost a b
  constructor
  · rw [signedLookupModularAddProgram,ht,ht,h.1]; omega
  · rw [signedLookupModularAddProgram,modularMeasurements_seq,modularMeasurements_seq,h.2]; omega

theorem signedLookupModularAddState_ready (table : Nat → Nat) (bits paths input acc : List Wire)
    (correction : List Bool) (p : Nat) (q sign c r t f : Wire)
    (hd : (q::bits++paths).Disjoint input) (ha : paths.Disjoint acc) (hb : bits.Disjoint acc)
    (hlen : input.length=acc.length) (hne : 0<acc.length) (hk : acc.length=correction.length)
    (hnd : ([q,c,r,t,f]++input++acc).Nodup) (hneg : ([sign,c,r,t,f]++acc++input).Nodup)
    (hp0 : 0<p) (hp : p<2^acc.length) (hconstant : boolWordToNat correction=2^acc.length-p)
    (hv : ∀ label, table label<p) (s : BasisState) (hs : LookupModularValid paths input acc p q c r t f s) :
    LookupModularValid paths input acc p q c r t f
      (signedLookupModularAddState table bits input acc correction p q sign c f s) := by
  have h := signedLookupModularAddState_correct table bits paths input acc correction p q sign c r t f
    hd ha hb hlen hne hk hnd hneg hp0 hp hconstant hv s hs
  apply lookup_valid_update paths input acc p q c r t f hnd ha s _ hs h.2
  rw [h.1]
  split <;> exact Nat.mod_lt _ hp0

end
end ShorECDLP.Paper2607_13816
