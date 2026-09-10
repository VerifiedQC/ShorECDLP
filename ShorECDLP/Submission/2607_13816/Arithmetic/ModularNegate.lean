import ShorECDLP.Submission.«2607_13816».Arithmetic.SquareCoherent
import ShorECDLP.Submission.«2607_13816».Arithmetic.ConstMinus
import ShorECDLP.Submission.«2607_13816».Arithmetic.ConstantModular
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
private theorem negation_arithmetic (B p y : Nat) (q : Bool) (hp : p<B) (hy : y<p) :
    let flag := q && decide (1≤y)
    let flipped := if q then B-1-y else y
    let low := (flipped+(if q then 1 else 0))%B
    let out := (low+(if flag then p else 0))%B
    out=(if q then (p-y)%p else y) ∧ flag=(q && decide (1≤out)) := by
  cases q with
  | false => simp [Nat.mod_eq_of_lt (show y<B by omega)]
  | true =>
    by_cases hz : y=0
    · subst y
      have he : B-1+1=B := by omega
      simp [he]
    · have he : B-1-y+1=B-y := by omega
      have hlo : B-y<B := by omega
      have hp0 : 0<p := by omega
      have hpn : p-y<p := by omega
      have hbig : B-y+p=B+(p-y) := by omega
      simp only [Bool.true_and,if_true,he,decide_eq_true (show 1≤y by omega),Nat.mod_eq_of_lt hlo]
      rw [hbig,Nat.add_mod_left,Nat.mod_eq_of_lt (show p-y<B by omega),Nat.mod_eq_of_lt hpn]
      simp [show 1≤p-y by omega]
def modularNegateIdealState (target : List Wire) (modulus : List Bool) (q f : Wire) (s : BasisState) : BasisState :=
  let flagged := upd s f (Bool.xor (s f) (s q && decide (1≤boolWordToNat (wireValues target s))))
  let flipped := fun w => if w ∈ target then flagged w ^^ flagged q else flagged w
  let increment := gidneyAddIdealState target ((List.range target.length).map (Nat.testBit 1)) q flipped
  let mid := gidneyAddIdealState target modulus f increment
  upd mid f (Bool.xor (mid f) (mid q && decide (1≤boolWordToNat (wireValues target mid))))
private theorem negate_word_upd (target : List Wire) (s : BasisState) (f : Wire) (b : Bool)
    (hf : f ∉ target) : wireValues target (upd s f b)=wireValues target s := by
  apply List.map_congr_left
  intro w hw
  have hn : w≠f := fun he => hf (he ▸ hw)
  simp [upd,hn]

theorem modularNegateIdealState_correct (target : List Wire) (modulus : List Bool) (p : Nat)
    (q f : Wire) (s : BasisState) (hn : 0<target.length) (hk : target.length=modulus.length)
    (hnd : target.Nodup) (hq : q ∉ target) (hf : f ∉ target) (hqf : q≠f)
    (hclean : s f=false) (hp : p<2^target.length) (hy : boolWordToNat (wireValues target s)<p)
    (hmodulus : boolWordToNat modulus=p) :
    boolWordToNat (wireValues target (modularNegateIdealState target modulus q f s))=
      (if s q then (p-boolWordToNat (wireValues target s))%p else boolWordToNat (wireValues target s)) ∧
    ∀ w, w ∉ target → modularNegateIdealState target modulus q f s w=s w := by
  let B := 2^target.length
  let y := boolWordToNat (wireValues target s)
  let flag := s q && decide (1≤y)
  let flagged := upd s f (Bool.xor (s f) flag)
  let flipped : BasisState := fun w => if w ∈ target then flagged w ^^ flagged q else flagged w
  let inc := gidneyAddIdealState target ((List.range target.length).map (Nat.testBit 1)) q flipped
  let mid := gidneyAddIdealState target modulus f inc
  have hflag : flagged f=flag := by simp [flagged,hclean]
  have hq0 : flagged q=s q := by simp [flagged,upd,hqf]
  have hword : wireValues target flagged=wireValues target s := negate_word_upd target s f _ hf
  have hflipq : flipped q=s q := by simp [flipped,hq,hq0]
  have hflipf : flipped f=flag := by simp [flipped,hf,hflag]
  have hflip : boolWordToNat (wireValues target flipped)=(if s q then B-1-y else y) := by
    cases hh : s q with
    | false =>
      have he : wireValues target flipped=wireValues target s := by
        rw [← hword]
        apply List.map_congr_left
        intro w hw
        simp [flipped,hq0,hh]
      simp [he,y]
    | true =>
      have he : wireValues target flipped=(wireValues target s).map Bool.not := by
        rw [← hword]
        simp only [wireValues,List.map_map]
        apply List.map_congr_left
        intro w hw
        simp [flipped,hw,hq0,hh]
      have hb := boolWordToNat_map_not_add (wireValues target s)
      have hlen : (wireValues target s).length=target.length := by simp [wireValues]
      rw [hlen] at hb
      rw [he]
      simp only [if_true]
      dsimp only [B,y]
      omega
  have hi := gidneyAddIdealState_correct target ((List.range target.length).map (Nat.testBit 1)) q flipped (by simp) hnd
  have hm := gidneyAddIdealState_correct target modulus f inc hk hnd
  have hone : boolWordToNat ((List.range target.length).map (Nat.testBit 1))=1 :=
    gidneyCompareBits_value target.length 1 (Nat.one_lt_two_pow hn.ne')
  have hiq : inc q=s q := (hi.2 q hq).trans hflipq
  have hif : inc f=flag := (hi.2 f hf).trans hflipf
  have hmq : mid q=s q := (hm.2 q hq).trans hiq
  have hmf : mid f=flag := (hm.2 f hf).trans hif
  have hvalue : boolWordToNat (wireValues target mid)=
      (((if s q then B-1-y else y)+(if s q then 1 else 0))%B+(if flag then p else 0))%B := by
    rw [hm.1,hi.1,hif,hmodulus,hone,hflip,hflipq]
  have hmath := negation_arithmetic B p y (s q) hp hy
  have hclear : Bool.xor (mid f) (mid q && decide (1≤boolWordToNat (wireValues target mid)))=false := by
    rw [hmf,hmq,hvalue,← hmath.2]
    exact Bool.xor_self _
  change boolWordToNat (wireValues target (upd mid f _))=_ ∧ ∀ w, w ∉ target → upd mid f _ w=s w
  rw [hclear]
  constructor
  · rw [negate_word_upd target mid f false hf,hvalue]
    exact hmath.1
  · intro w hw
    by_cases he : w=f
    · subst w; simp [upd,hclean]
    · rw [upd_other _ _ _ he]
      exact (hm.2 w hw).trans ((hi.2 w hw).trans (by simp [flipped,hw,flagged,upd,he]))

/-- Source modular negation: detect nonzero, complement and increment,
conditionally add p, then erase the nonzero flag. -/
def controlledModularNegate (target dirty : List Wire) (modulus : List Bool)
    (q c r t f : Wire) : AdaptiveCircuit :=
  (controlledGidneyCompareGE target dirty 1 q c r t f).seq
    (.unitary (controlledComplement target q)
      ((controlledGidneyAddConst target (dirty.take (target.length-1))
        ((List.range target.length).map (Nat.testBit 1)) q c r t).seq
        ((controlledGidneyAddConst target (dirty.take (target.length-1)) modulus f c r t).seq
          (controlledGidneyCompareGE target dirty 1 q c r t f))))

theorem controlledModularNegate_wellFormed (target dirty : List Wire) (modulus : List Bool)
    (q c r t f : Wire) (hk : target.length=modulus.length) (hd : target.length=dirty.length)
    (hn : 0<target.length) (hnd : ([q,c,r,t,f]++target++dirty).Nodup) :
    (controlledModularNegate target dirty modulus q c r t f).WellFormed := by
  have hl := constantModular_layout target dirty q c r t f hnd
  have htake : target.length=(dirty.take (target.length-1)).length+1 := by simp only [List.length_take]; omega
  have hq : q ∉ target := by
    intro hh
    exact (List.nodup_append.mp (List.nodup_append.mp hnd).1).2.2 q (by simp) q hh rfl
  refine (controlledGidneyCompareGE_wellFormed target dirty 1 q c r t f hd hnd).seq ⟨?_,?_⟩
  · intro gate hg
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hg
    exact fun he => hq (he ▸ hw)
  · exact (controlledGidneyAddConst_wellFormed target _ _ q c r t (by simp) htake hl.1).seq
      ((controlledGidneyAddConst_wellFormed target _ modulus f c r t hk htake hl.2.1).seq
        (controlledGidneyCompareGE_wellFormed target dirty 1 q c r t f hd hnd))

theorem controlledModularNegate_branch_correct (target dirty : List Wire) (modulus : List Bool)
    (q c r t f : Wire) (s : BasisState) (hk : target.length=modulus.length)
    (hd : target.length=dirty.length) (hn : 0<target.length)
    (hnd : ([q,c,r,t,f]++target++dirty).Nodup)
    (hc : s c=false) (hr : s r=false) (ht : s t=false)
    (b : InstrumentBranch) (hb : b ∈ (controlledModularNegate target dirty modulus q c r t f).run) :
    b.kraus (ket s)=registerXResetMagnitude b.history.length • ket (modularNegateIdealState target modulus q f s) := by
  have hl := constantModular_layout target dirty q c r t f hnd
  have htake : target.length=(dirty.take (target.length-1)).length+1 := by simp only [List.length_take]; omega
  have htn := (List.nodup_append.mp (List.nodup_append.mp hnd).1).2.1
  have hsep (w : Wire) (hw : w ∈ [q,c,r,t,f]) : w ∉ target := by
    intro hh
    exact (List.nodup_append.mp (List.nodup_append.mp hnd).1).2.2 w hw w hh rfl
  have hneq (w : Wire) (hw : w ∈ [q,c,r,t]) : w≠f := by
    have hh : ([q,c,r,t]++[f]).Nodup := (List.nodup_append.mp (List.nodup_append.mp hnd).1).1
    exact fun he => (List.nodup_append.mp hh).2.2 w hw f (by simp) he
  let flagged := upd s f (Bool.xor (s f) (s q && decide (1≤boolWordToNat (wireValues target s))))
  let flipped : BasisState := fun w => if w ∈ target then flagged w ^^ flagged q else flagged w
  let inc := gidneyAddIdealState target ((List.range target.length).map (Nat.testBit 1)) q flipped
  let mid := gidneyAddIdealState target modulus f inc
  have hflag (w : Wire) (hw : w ∈ [q,c,r,t]) : flagged w=s w := by simp [flagged,upd,hneq w hw]
  have hflip (w : Wire) (hw : w ∈ [q,c,r,t]) : flipped w=s w := by
    simp only [flipped,if_neg (hsep w (by simp only [List.mem_cons,List.not_mem_nil] at hw ⊢; tauto))]
    exact hflag w hw
  have hi := gidneyAddIdealState_correct target ((List.range target.length).map (Nat.testBit 1)) q flipped (by simp) htn
  have hm := gidneyAddIdealState_correct target modulus f inc hk htn
  have hmid (w : Wire) (hw : w ∈ [q,c,r,t]) : mid w=s w :=
    (hm.2 w (hsep w (by simp only [List.mem_cons,List.not_mem_nil] at hw ⊢; tauto))).trans
      ((hi.2 w (hsep w (by simp only [List.mem_cons,List.not_mem_nil] at hw ⊢; tauto))).trans (hflip w hw))
  apply horner_seq_branch _ _ s flagged _ ?_ ?_ b hb
  · intro b hb
    have hh := controlledGidneyCompareGE_branch_correct target dirty 1 q c r t f s hd hnd hc hr ht b hb
    rw [hh.1]; exact hh.2
  · intro b hb
    obtain ⟨after,ha,hh,htransfer⟩ := gidneyUnitaryBranch (controlledComplement target q) _ b hb
    have hrest : after.kraus (ket flipped)=registerXResetMagnitude after.history.length •
        ket (modularNegateIdealState target modulus q f s) := by
      apply horner_seq_branch _ _ flipped inc _ ?_ ?_ after ha
      · intro b hb
        have hh := controlledGidneyAddConst_branch_correct target _ _ q c r t flipped (by simp) htake hl.1
          ((hflip c (by simp)).trans hc) ((hflip r (by simp)).trans hr) ((hflip t (by simp)).trans ht) b hb
        rw [hh.1]; exact hh.2
      · intro b hb
        apply horner_seq_branch _ _ inc mid _ ?_ ?_ b hb
        · intro b hb
          have hic (w : Wire) (hw : w ∈ [q,c,r,t]) : inc w=s w :=
            (hi.2 w (hsep w (by simp only [List.mem_cons,List.not_mem_nil] at hw ⊢; tauto))).trans (hflip w hw)
          have hh := controlledGidneyAddConst_branch_correct target _ modulus f c r t inc hk htake hl.2.1
            ((hic c (by simp)).trans hc) ((hic r (by simp)).trans hr) ((hic t (by simp)).trans ht) b hb
          rw [hh.1]; exact hh.2
        · intro b hb
          have hh := controlledGidneyCompareGE_branch_correct target dirty 1 q c r t f mid hd hnd
            ((hmid c (by simp)).trans hc) ((hmid r (by simp)).trans hr) ((hmid t (by simp)).trans ht) b hb
          rw [hh.1]; exact hh.2
    rw [hh,htransfer,Quantum.run_ket_agrees_classical _ _ (by simp [controlledComplement,HPFree])]
    rw [controlledComplement_state target q flagged htn (hsep q (by simp))]
    exact hrest

/-- Canonical target and clean helpers; control and borrowed dirty bank are arbitrary. -/
def ModularNegateValid (target : List Wire) (p : Nat) (c r t f : Wire) (s : BasisState) : Prop :=
  s c=false ∧ s r=false ∧ s t=false ∧ s f=false ∧ boolWordToNat (wireValues target s)<p

theorem controlledModularNegate_coherent (target dirty : List Wire) (modulus : List Bool)
    (p : Nat) (q c r t f : Wire) (hk : target.length=modulus.length) (hd : target.length=dirty.length)
    (hn : 0<target.length) (hnd : ([q,c,r,t,f]++target++dirty).Nodup) (hp0 : 0<p) :
    CoherentlyImplementsOn (controlledModularNegate target dirty modulus q c r t f)
      (Finsupp.lmapDomain ℂ ℂ (modularNegateIdealState target modulus q f))
      (ModularNegateValid target p c r t f) := by
  have hz (ws : List Wire) : boolWordToNat (wireValues ws (fun _ => false))=0 := by
    induction ws with
    | nil => rfl
    | cons w ws ih => simpa [wireValues,boolWordToNat] using ih
  apply coherent_history_branches _ _ _
    (controlledModularNegate_wellFormed target dirty modulus q c r t f hk hd hn hnd)
    (fun _ => false) ?_ ?_
  · exact ⟨rfl,rfl,rfl,rfl,by rw [hz]; exact hp0⟩
  · intro b hb s hs
    exact controlledModularNegate_branch_correct target dirty modulus q c r t f s hk hd hn hnd
      hs.1 hs.2.1 hs.2.2.1 b hb

end ShorECDLP.Paper2607_13816
