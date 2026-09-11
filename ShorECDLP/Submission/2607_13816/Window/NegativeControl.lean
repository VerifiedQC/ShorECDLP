import ShorECDLP.Submission.«2607_13816».Arithmetic.ModularNegate
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section

def flipControl (q : Wire) (s : BasisState) : BasisState := fun w => if w=q then !s q else s w

private theorem flipControl_ket (q : Wire) (s : BasisState) :
    Quantum.run [Gate.X q] (ket s)=ket (flipControl q s) := by
  rw [Quantum.run_ket_agrees_classical _ _ (by simp [HPFree])]
  rfl

@[simp] theorem flipControl_involution (q : Wire) (s : BasisState) : flipControl q (flipControl q s)=s := by
  funext w
  by_cases h : w=q <;> simp [flipControl,h]

def negativeControlledModularNegate (target dirty : List Wire) (modulus : List Bool)
    (q c r t f : Wire) : AdaptiveCircuit :=
  ((AdaptiveCircuit.unitary [Gate.X q] .done).seq
    (controlledModularNegate target dirty modulus q c r t f)).seq (.unitary [Gate.X q] .done)

def negativeModularNegateState (target : List Wire) (modulus : List Bool) (q f : Wire)
    (s : BasisState) : BasisState :=
  flipControl q (modularNegateIdealState target modulus q f (flipControl q s))

private theorem flip_negate_valid (target : List Wire) (p : Nat) (q c r t f : Wire)
    (hq : q∉target) (hne : q≠c ∧ q≠r ∧ q≠t ∧ q≠f)
    (s : BasisState) (hs : ModularNegateValid target p c r t f s) :
    ModularNegateValid target p c r t f (flipControl q s) := by
  have hw : wireValues target (flipControl q s)=wireValues target s := by
    apply List.map_congr_left
    intro w hw
    have hn : w≠q := fun he => hq (he ▸ hw)
    simp [flipControl,hn]
  exact ⟨by simpa [flipControl,hne.1.symm] using hs.1,
    by simpa [flipControl,hne.2.1.symm] using hs.2.1,
    by simpa [flipControl,hne.2.2.1.symm] using hs.2.2.1,
    by simpa [flipControl,hne.2.2.2.symm] using hs.2.2.2.1,
    by rw [hw]; exact hs.2.2.2.2⟩

private theorem flip_coherent (q : Wire) :
    CoherentlyImplementsOn (.unitary [Gate.X q] .done)
      (Finsupp.lmapDomain ℂ ℂ (flipControl q)) (fun _ => True) := by
  apply (CoherentlyImplementsOn.unitary [Gate.X q] (fun _ => True)).congrIdeal
  intro s _
  simpa [ket] using flipControl_ket q s

theorem negativeControlledModularNegate_coherent (target dirty : List Wire) (modulus : List Bool)
    (p : Nat) (q c r t f : Wire) (hk : target.length=modulus.length) (hd : target.length=dirty.length)
    (hn : 0<target.length) (hnd : ([q,c,r,t,f]++target++dirty).Nodup) (hp0 : 0<p) :
    CoherentlyImplementsOn (negativeControlledModularNegate target dirty modulus q c r t f)
      (Finsupp.lmapDomain ℂ ℂ (negativeModularNegateState target modulus q f))
      (ModularNegateValid target p c r t f) := by
  have hsep := (List.nodup_cons.mp hnd).1
  change q∉([c,r,t,f]++target++dirty) at hsep
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or] at hsep
  have hq : q∉target := hsep.1.2
  have hne : q≠c ∧ q≠r ∧ q≠t ∧ q≠f := hsep.1.1
  have hf : CoherentlyImplementsOn (.unitary [Gate.X q] .done)
      (Finsupp.lmapDomain ℂ ℂ (flipControl q)) (ModularNegateValid target p c r t f) := by
    obtain ⟨cs,hc,hm⟩ := flip_coherent q
    exact ⟨cs,hc.imp (fun b c hb s _ => hb s trivial),hm⟩
  have body := controlledModularNegate_coherent target dirty modulus p q c r t f hk hd hn hnd hp0
  have first := hf.seq body (by
    intro s hs
    simpa [ket] using supportedOn_ket _ _ (flip_negate_valid target p q c r t f hq hne s hs))
  have all := first.seq (flip_coherent q) (by
    intro s hs
    simpa [LinearMap.comp_apply,ket] using
      supportedOn_ket (fun _ => True) (modularNegateIdealState target modulus q f (flipControl q s)) trivial)
  apply all.congrIdeal
  intro s hs
  simp [LinearMap.comp_apply,ket,negativeModularNegateState]
private theorem flipControl_word (target : List Wire) (q : Wire) (hq : q∉target) (s : BasisState) :
    wireValues target (flipControl q s)=wireValues target s := by
  apply List.map_congr_left
  intro w hw
  have hn : w≠q := fun he => hq (he ▸ hw)
  simp [flipControl,hn]

theorem negativeModularNegateState_correct (target : List Wire) (modulus : List Bool) (p : Nat)
    (q f : Wire) (s : BasisState) (hn : 0<target.length) (hk : target.length=modulus.length)
    (hnd : target.Nodup) (hq : q∉target) (hf : f∉target) (hqf : q≠f)
    (hclean : s f=false) (hp : p<2^target.length) (hy : boolWordToNat (wireValues target s)<p)
    (hmodulus : boolWordToNat modulus=p) :
    boolWordToNat (wireValues target (negativeModularNegateState target modulus q f s))=
      (if s q then boolWordToNat (wireValues target s) else (p-boolWordToNat (wireValues target s))%p) ∧
    ∀ w, w∉target → negativeModularNegateState target modulus q f s w=s w := by
  have h := modularNegateIdealState_correct target modulus p q f (flipControl q s) hn hk hnd hq hf hqf
    (by simpa [flipControl,hqf.symm] using hclean) hp
    (by rw [flipControl_word target q hq]; exact hy) hmodulus
  constructor
  · rw [negativeModularNegateState,flipControl_word target q hq,h.1,flipControl_word target q hq]
    cases hs : s q <;> simp [flipControl,hs]
  · intro w hw
    by_cases hwq : w=q
    · subst w
      simp [negativeModularNegateState,flipControl,h.2 q hq]
    · simp [negativeModularNegateState,flipControl,hwq,h.2 w hw]

private theorem negate_value_involution (p value : Nat) (hv : value<p) :
    (p-(p-value)%p)%p=value := by
  by_cases hz : value=0
  · simp [hz]
  · have hl : p-value<p := by omega
    rw [Nat.mod_eq_of_lt hl,show p-(p-value)=value by omega,Nat.mod_eq_of_lt hv]

theorem negativeModularNegateState_involution (target : List Wire) (modulus : List Bool) (p : Nat)
    (q f : Wire) (s : BasisState) (hn : 0<target.length) (hk : target.length=modulus.length)
    (hnd : target.Nodup) (hq : q∉target) (hf : f∉target) (hqf : q≠f)
    (hclean : s f=false) (hp : p<2^target.length) (hy : boolWordToNat (wireValues target s)<p)
    (hmodulus : boolWordToNat modulus=p) :
    negativeModularNegateState target modulus q f (negativeModularNegateState target modulus q f s)=s := by
  let after := negativeModularNegateState target modulus q f s
  have h1 := negativeModularNegateState_correct target modulus p q f s hn hk hnd hq hf hqf hclean hp hy hmodulus
  have hp0 : 0<p := by omega
  have ha : boolWordToNat (wireValues target after)<p := by
    rw [h1.1]
    split
    · exact hy
    · exact Nat.mod_lt _ hp0
  have h2 := negativeModularNegateState_correct target modulus p q f after hn hk hnd hq hf hqf
    ((h1.2 f hf).trans hclean) hp ha hmodulus
  have he : boolWordToNat (wireValues target (negativeModularNegateState target modulus q f after))=
      boolWordToNat (wireValues target s) := by
    rw [h2.1]
    dsimp only [after]
    rw [h1.2 q hq,h1.1]
    cases hs : s q
    · simp only [Bool.false_eq_true,if_false]
      exact negate_value_involution p _ hy
    · simp
  have he' := boolWordToNat_injective_of_length (by simp [wireValues]) he
  funext w
  by_cases hw : w∈target
  · exact List.map_inj_left.mp he' w hw
  · exact (h2.2 w hw).trans (h1.2 w hw)

theorem negativeControlledModularNegate_resources (target dirty : List Wire) (modulus : List Bool)
    (q c r t f : Wire) :
    (negativeControlledModularNegate target dirty modulus q c r t f).tCount=
      (controlledModularNegate target dirty modulus q c r t f).tCount ∧
    (negativeControlledModularNegate target dirty modulus q c r t f).measurementCount=
      (controlledModularNegate target dirty modulus q c r t f).measurementCount := by
  have ht (a b : AdaptiveCircuit) : (a.seq b).tCount=a.tCount+b.tCount := by
    simpa only [gidneyGateCount_tCount] using modularGateCount_seq tCost a b
  constructor
  · rw [negativeControlledModularNegate,ht,ht]
    change (0+_)+0=_
    omega
  · rw [negativeControlledModularNegate,modularMeasurements_seq,modularMeasurements_seq]
    change (0+_)+0=_
    omega

theorem negativeControlledModularNegate_wires (target dirty : List Wire) (modulus : List Bool)
    (q c r t f : Wire) :
    (negativeControlledModularNegate target dirty modulus q c r t f).wires ⊆
      q::(controlledModularNegate target dirty modulus q c r t f).wires := by
  intro w hw
  simp only [negativeControlledModularNegate,modularWires_seq] at hw
  rcases hw with (hw | hw) | hw
  · simpa [AdaptiveCircuit.wires,circuitWires,gateWires] using Or.inl hw
  · exact List.mem_cons_of_mem q hw
  · simpa [AdaptiveCircuit.wires,circuitWires,gateWires] using Or.inl hw

end
end ShorECDLP.Paper2607_13816
