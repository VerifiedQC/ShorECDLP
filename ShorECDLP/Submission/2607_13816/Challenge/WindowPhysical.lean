import ShorECDLP.Submission.«2607_13816».Challenge.BatchTemplate
import ShorECDLP.Submission.«2607_13816».Challenge.PreparedBatch
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem literalProgram_wellFormed {n s : Nat} (gs : Circuit) (h : CircuitWellFormed gs) :
    (literalProgram (n:=n) (s:=s) gs).WellFormed := by
  apply gateProgram_wellFormed
  intro g hg
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hg
  exact h v hv

theorem appendCompiled_wellFormed {n start : Nat} (p : (count : Nat) × Straight n start (start+count))
    (q : (count : Nat) × Straight n (start+p.1) (start+p.1+count))
    (hp : p.2.WellFormed) (hq : q.2.WellFormed) : (appendCompiled p q).2.WellFormed := by
  simpa only [appendCompiled,castFinish_wellFormed] using straight_append_wellFormed p.2 q.2 hp hq

theorem prependCompiled_wellFormed {n start : Nat} (gs : Circuit)
    (p : (count : Nat) × Straight n start (start+count))
    (hg : CircuitWellFormed gs) (hp : p.2.WellFormed) : (prependCompiled gs p).2.WellFormed :=
  straight_append_wellFormed _ _ (literalProgram_wellFormed gs hg) hp

theorem surroundCompiled_wellFormed {n start : Nat} (before after : Circuit)
    (p : (count : Nat) × Straight n start (start+count))
    (hb : CircuitWellFormed before) (ha : CircuitWellFormed after) (hp : p.2.WellFormed) :
    (surroundCompiled before after p).2.WellFormed :=
  prependCompiled_wellFormed _ _ hb (appendCompiled_wellFormed _ _ hp (literalProgram_wellFormed after ha))

theorem sequenceProgram_wellFormed (n : Nat) (ps : List (FixedSegment n))
    (hp : ∀ p∈ps,∀ start,(p start).2.WellFormed) (start : Nat) :
    (sequenceProgram n ps start).2.WellFormed := by
  induction ps generalizing start with
  | nil => trivial
  | cons p ps ih =>
    exact appendCompiled_wellFormed _ _ (hp p (by simp) start)
      (ih (fun q hq => hp q (by simp [hq])) _)

theorem reindexStraight_wellFormed {n m s e : Nat} (f : Fin n → Fin m) (p : Straight n s e) :
    (reindexStraight f p).WellFormed ↔ p.WellFormed := by
  have hg (g : TemplateGate n) : (reindexGate f g).WellFormed ↔ g.WellFormed := by
    cases g <;> rfl
  induction p with
  | done => rfl
  | gate g p ih => simp only [reindexStraight,Straight.WellFormed,hg,ih]
  | recordGate i v g p ih => simp only [reindexStraight,Straight.WellFormed,ih]
  | measure w p ih => exact ih

theorem reindexCompiled_wellFormed {n m start : Nat} (f : Fin n → Fin m)
    (p : (count : Nat) × Straight n start (start+count)) :
    (reindexCompiled f p).2.WellFormed ↔ p.2.WellFormed :=
  reindexStraight_wellFormed f p.2

theorem registerCorrectionProgram_wellFormed {n s e : Nat} (ws : List Wire)
    (indices : List (Fin s)) (next : Straight n s e) (hn : next.WellFormed) :
    (registerCorrectionProgram ws indices next).WellFormed := by
  induction ws generalizing indices with
  | nil => exact hn
  | cons w ws ih =>
    cases indices with
    | nil => exact hn
    | cons i is =>
      exact recordGates_wellFormed i (pauliZ w) _ (by simp [pauliZ,CircuitWellFormed,Gate.WellFormed]) (ih is)

theorem deferredCorrectionProgram_wellFormed (n : Nat) (targets : List Wire) (cleanup : Circuit)
    (cells : List (Circuit × Wire)) (hc : CircuitWellFormed cleanup)
    (hcs : ∀ cell ∈ cells, CircuitWellFormed cell.1) (start : Nat) (prior : List (Fin start)) :
    (deferredCorrectionProgram n targets cleanup cells start prior).WellFormed := by
  induction cells generalizing start with
  | nil =>
    exact registerCorrectionProgram_wellFormed _ _ _
      (straight_append_wellFormed _ _ (literalProgram_wellFormed cleanup hc)
        (registerCorrectionProgram_wellFormed _ _ _ trivial))
  | cons cell cells ih =>
    rcases cell with ⟨gs,w⟩
    simp only [deferredCorrectionProgram,castFinish_wellFormed]
    exact straight_append_wellFormed _ _ (literalProgram_wellFormed gs (hcs (gs,w) (by simp)))
      (ih (fun c h => hcs c (by simp [h])) _ _)

theorem deferredCorrectionCircuit_physical (targets : List Wire) (cleanup : Circuit)
    (cells : List (Circuit × Wire)) (outcomes : List Bool)
    (h : (deferredCorrectionCircuit targets cleanup cells outcomes).WellFormed) :
    CircuitWellFormed cleanup ∧ ∀ cell∈cells,CircuitWellFormed cell.1 := by
  induction cells generalizing outcomes with
  | nil =>
    have hc := h.1
    simp only [CircuitWellFormed,List.forall_mem_append] at hc
    exact ⟨hc.1.2,by simp⟩
  | cons cell cells ih =>
    rcases cell with ⟨gs,w⟩
    obtain ⟨hc,ht⟩ := ih (outcomes++[false]) h.2.1
    exact ⟨hc,by intro c hm; rcases List.mem_cons.mp hm with rfl|hm; exact h.1; exact ht c hm⟩

theorem deferredCorrectionProgram_wellFormed_of_source (n : Nat) (targets : List Wire) (cleanup : Circuit)
    (cells : List (Circuit × Wire)) (outcomes : List Bool)
    (h : (deferredCorrectionCircuit targets cleanup cells outcomes).WellFormed)
    (start : Nat) (prior : List (Fin start)) :
    (deferredCorrectionProgram n targets cleanup cells start prior).WellFormed := by
  obtain ⟨hc,ht⟩ := deferredCorrectionCircuit_physical targets cleanup cells outcomes h
  exact deferredCorrectionProgram_wellFormed n targets cleanup cells hc ht start prior

theorem gidneyNontrivialProgram_wellFormed (n start : Nat) (a d q carry spare ancilla : Wire)
    (as ds : List Wire) (k : Bool) (ks : List Bool)
    (hd : as.length = ds.length+1) (hk : ks.length=as.length)
    (hnz : (k::ks).all (fun b => !b)=false)
    (h : (controlledGidneyAddConst (a::as) (d::ds) (k::ks) q carry spare ancilla).WellFormed) :
    (gidneyNontrivialProgram n start a d q carry spare ancilla as ds k ks).WellFormed := by
  have hh : CircuitWellFormed (gidneyAddCarryCell q carry spare ancilla a d k) ∧
      (deferredCorrectionCircuit (d::ds) (gidneyAddCleanup (a::as) (d::ds) (k::ks) q carry)
        (gidneyCarryCells q spare carry ancilla as ds ks) List.nil).WellFormed := by
    rw [← gidneyCarryCells_source q spare carry ancilla as ds ks _ _ List.nil hd hk]
    cases as with
    | nil => simp at hd
    | cons b bs => simpa only [controlledGidneyAddConst,hnz,Bool.false_eq_true,if_false,
        AdaptiveCircuit.WellFormed] using h
  exact straight_append_wellFormed _ _ (literalProgram_wellFormed _ hh.1)
    (deferredCorrectionProgram_wellFormed_of_source n _ _ _ List.nil hh.2 start List.nil)

theorem gidneyProgram_wellFormed_of_source (n start : Nat) (input dirty : List Wire) (constant : List Bool)
    (q carry spare ancilla : Wire) (hd : input.length=dirty.length+1) (hk : constant.length=input.length)
    (h : (controlledGidneyAddConst input dirty constant q carry spare ancilla).WellFormed) :
    (gidneyProgram n start input dirty constant q carry spare ancilla).2.WellFormed := by
  let WF : ((count : Nat) × Straight n start (start+count)) → Prop := fun p => p.2.WellFormed
  change WF (gidneyProgram n start input dirty constant q carry spare ancilla)
  unfold gidneyProgram
  split
  · trivial
  · rename_i hz
    have hnz : constant.all (fun k => !k)=false := Bool.eq_false_iff.mpr hz
    cases input with
    | nil => simp at hd
    | cons a as =>
      cases constant with
      | nil => simp at hk
      | cons k ks =>
        cases dirty with
        | nil =>
          have ha : as=[] := List.eq_nil_of_length_eq_zero (by simpa using hd)
          subst as
          have hks : ks=[] := List.eq_nil_of_length_eq_zero (by simpa using hk)
          subst ks
          dsimp only [WF]
          apply literalProgram_wellFormed
          have hh := h
          unfold controlledGidneyAddConst at hh
          simp only [hnz,Bool.false_eq_true,if_false,AdaptiveCircuit.WellFormed] at hh
          exact hh.1
        | cons d ds =>
          cases as with
          | nil => simp at hd
          | cons b bs =>
            dsimp only [WF]
            exact gidneyNontrivialProgram_wellFormed n start a d q carry spare ancilla (b::bs) ds k ks
              (by simpa using hd) (by simpa using hk) hnz h

theorem gidneyProgram_wellFormed (n start : Nat) (input dirty : List Wire) (constant : List Bool)
    (q carry spare ancilla : Wire) (hd : input.length=dirty.length+1) (hk : constant.length=input.length)
    (hnd : ([q,carry,spare,ancilla]++input++dirty).Nodup) :
    (gidneyProgram n start input dirty constant q carry spare ancilla).2.WellFormed :=
  gidneyProgram_wellFormed_of_source n start input dirty constant q carry spare ancilla hd hk
    (controlledGidneyAddConst_wellFormed input dirty constant q carry spare ancilla hk.symm hd hnd)

theorem compareCarryCells_wellFormed (q current spare ancilla flag : Wire)
    (input dirty : List Wire) (constant : List Bool) (targets : List Wire)
    (cleanup : Circuit) (outcomes : List Bool)
    (hd : input.length=dirty.length) (hk : constant.length=input.length)
    (h : (gidneyCompareTail q current spare ancilla flag
      (fun bs => registerZCorrection targets bs ++ cleanup ++ registerZCorrection targets bs)
      outcomes input dirty constant).WellFormed) :
    (deferredCorrectionCircuit targets cleanup
      (compareCarryCells q current spare ancilla flag input dirty constant) outcomes).WellFormed := by
  induction input generalizing current spare dirty constant outcomes with
  | nil =>
    have hd' : dirty=[] := List.eq_nil_of_length_eq_zero hd.symm
    have hk' : constant=[] := List.eq_nil_of_length_eq_zero hk
    subst dirty
    subst constant
    exact ⟨by simp [CircuitWellFormed],h⟩
  | cons a input ih =>
    cases dirty with
    | nil => simp at hd
    | cons d dirty =>
      cases constant with
      | nil => simp at hk
      | cons k constant =>
        exact ⟨h.1,ih spare current dirty constant (outcomes++[false]) (by simpa using hd)
          (by simpa using hk) h.2.1,
          ih spare current dirty constant (outcomes++[true]) (by simpa using hd)
          (by simpa using hk) h.2.2⟩

theorem compareCarryProgram_wellFormed_of_source (n start : Nat) (a d q carry spare ancilla flag : Wire)
    (input dirty : List Wire) (k : Bool) (constant : List Bool)
    (hd : input.length=dirty.length) (hk : constant.length=input.length)
    (h : (controlledGidneyCompareCarry (a::input) (d::dirty) (k::constant) q carry spare ancilla flag).WellFormed) :
    (compareCarryProgram n start a d q carry spare ancilla flag input dirty k constant).WellFormed := by
  have hh := compareCarryCells_wellFormed q spare carry ancilla flag input dirty constant (d::dirty)
    (controlledConstCarryXor (a::input) (d::dirty) (k::constant) q carry) List.nil hd hk h.2
  exact straight_append_wellFormed _ _ (literalProgram_wellFormed _ h.1)
    (deferredCorrectionProgram_wellFormed_of_source n _ _ _ List.nil hh start List.nil)

theorem compareCoreProgram_wellFormed_of_source (n start : Nat) (input dirty : List Wire) (constant : List Bool)
    (q carry spare ancilla flag : Wire) (hd : input.length=dirty.length) (hk : constant.length=input.length)
    (h : (controlledGidneyCompareCarry input dirty constant q carry spare ancilla flag).WellFormed) :
    (compareCoreProgram n start input dirty constant q carry spare ancilla flag).2.WellFormed := by
  cases input with
  | nil => trivial
  | cons a input =>
    cases dirty with
    | nil => simp at hd
    | cons d dirty =>
      cases constant with
      | nil => simp at hk
      | cons k constant =>
        exact compareCarryProgram_wellFormed_of_source n start a d q carry spare ancilla flag input dirty k constant
          (by simpa using hd) (by simpa using hk) h

theorem compareGEProgram_wellFormed_of_source (n start : Nat) (input dirty : List Wire) (threshold : Nat)
    (q carry spare ancilla flag : Wire) (hd : input.length=dirty.length)
    (h : (controlledGidneyCompareGE input dirty threshold q carry spare ancilla flag).WellFormed) :
    (compareGEProgram n start input dirty threshold q carry spare ancilla flag).2.WellFormed := by
  let WF : ((count : Nat) × Straight n start (start+count)) → Prop := fun p => p.2.WellFormed
  change WF (compareGEProgram n start input dirty threshold q carry spare ancilla flag)
  unfold compareGEProgram
  split
  · rename_i hz
    exact literalProgram_wellFormed _ (by simpa only [controlledGidneyCompareGE,if_pos hz,
      AdaptiveCircuit.WellFormed,and_true] using h)
  · rename_i hz
    split
    · trivial
    · rename_i hh
      apply compareCoreProgram_wellFormed_of_source _ _ _ _ _ _ _ _ _ _ hd (by simp)
      simpa only [controlledGidneyCompareGE,if_neg hz,if_neg hh] using h

theorem compareGEProgram_wellFormed (n start : Nat) (input dirty : List Wire) (threshold : Nat)
    (q carry spare ancilla flag : Wire) (hd : input.length=dirty.length)
    (hnd : ([q,carry,spare,ancilla,flag]++input++dirty).Nodup) :
    (compareGEProgram n start input dirty threshold q carry spare ancilla flag).2.WellFormed :=
  compareGEProgram_wellFormed_of_source n start input dirty threshold q carry spare ancilla flag hd
    (controlledGidneyCompareGE_wellFormed input dirty threshold q carry spare ancilla flag hd hnd)

theorem modularNegateProgram_wellFormed (n start : Nat) (target dirty : List Wire) (modulus : List Bool)
    (q c r t f : Wire) (hk : target.length=modulus.length) (hd : target.length=dirty.length)
    (hn : 0<target.length) (hnd : ([q,c,r,t,f]++target++dirty).Nodup) :
    (modularNegateProgram n start target dirty modulus q c r t f).2.WellFormed := by
  have hl := constantModular_layout target dirty q c r t f hnd
  have htake : target.length=(dirty.take (target.length-1)).length+1 := by simp only [List.length_take]; omega
  have hq : q∉target := by
    intro hh
    exact (List.nodup_append.mp (List.nodup_append.mp hnd).1).2.2 q (by simp) q hh rfl
  unfold modularNegateProgram
  apply appendCompiled_wellFormed
  · exact compareGEProgram_wellFormed n start target dirty 1 q c r t f hd hnd
  · apply prependCompiled_wellFormed
    · intro gate hg
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hg
      exact fun he => hq (he ▸ hw)
    · apply appendCompiled_wellFormed
      · exact gidneyProgram_wellFormed _ _ _ _ _ q c r t htake (by simp) hl.1
      · apply appendCompiled_wellFormed
        · exact gidneyProgram_wellFormed _ _ _ _ _ f c r t htake hk.symm hl.2.1
        · exact compareGEProgram_wellFormed _ _ target dirty 1 q c r t f hd hnd

theorem negativeNegateProgram_wellFormed (n start : Nat) (target dirty : List Wire) (modulus : List Bool)
    (q c r t f : Wire) (hk : target.length=modulus.length) (hd : target.length=dirty.length)
    (hn : 0<target.length) (hnd : ([q,c,r,t,f]++target++dirty).Nodup) :
    (negativeNegateProgram n start target dirty modulus q c r t f).2.WellFormed :=
  prependCompiled_wellFormed _ _ (by simp [CircuitWellFormed,Gate.WellFormed])
    (appendCompiled_wellFormed _ _ (modularNegateProgram_wellFormed n start target dirty modulus q c r t f hk hd hn hnd)
      (literalProgram_wellFormed _ (by simp [CircuitWellFormed,Gate.WellFormed])))

theorem yNegateProgram_wellFormed (start : Nat) : (yNegateProgram start).2.WellFormed :=
  negativeNegateProgram_wellFormed _ _ _ _ _ _ _ _ _ _ (by simp [constantBits_length])
    (by simp) (by simp) (by decide +kernel)

theorem sharedYNegateProgram_wellFormed (w : OddWindow) (start : Nat) :
    (sharedYNegateProgram w start).2.WellFormed :=
  (reindexCompiled_wellFormed (windowIndex w) (yNegateProgram start)).mpr (yNegateProgram_wellFormed start)

attribute [local irreducible] modularNegateProgram

theorem xNegateProgram_wellFormed (n start : Nat) : (xNegateProgram n start).2.WellFormed := by
  unfold xNegateProgram
  apply modularNegateProgram_wellFormed n start (List.range' 263 256) (List.range' 7 256)
    (constantBits 256 ShorECDLP.p) 836 559 560 561 558 (by simp [constantBits_length]) (by simp) (by simp)
  rw [List.nodup_append,List.nodup_append]
  refine ⟨⟨by decide,by exact List.nodup_range',?_⟩,by exact List.nodup_range',?_⟩
  · intro a ha b hb he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    simp only [List.mem_range'_1] at hb
    dsimp only [Wire] at *
    omega
  · intro a ha b hb he
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1] at ha
    simp only [List.mem_range'_1] at hb
    dsimp only [Wire] at *
    omega
end ShorECDLP.Paper2607_13816.ChallengeMigration
