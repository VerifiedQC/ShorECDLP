import ShorECDLP.Submission.«2607_13816».Challenge.ArithmeticSupport
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

def templateControlSafe {n : Nat} (q : Wire) : TemplateGate n → Prop
  | .literal g | .whenBit _ _ g => constantControlSafe q g

def straightControlSafe {n s e : Nat} (q : Wire) : Straight n s e → Prop
  | .done => True
  | .gate g p => templateControlSafe q g ∧ straightControlSafe q p
  | .recordGate _ _ g p => constantControlSafe q g ∧ straightControlSafe q p
  | .measure w p => w ≠ q ∧ straightControlSafe q p

theorem constantStraight_support_erase {n s e : Nat} (q : Wire) (p : Straight n s e)
    (safe : straightControlSafe q p) (support : List Wire) (hp : straightWires p ⊆ q::support) :
    straightWires (constantStraight q p) ⊆ support := by
  have hg (g : Gate) (hs : constantControlSafe q g) (h : gateWires g ⊆ q::support) :
      gateWires (constantControlGate q g) ⊆ support := by
    intro w hw
    have hh := (constantControlGate_wires q g hs w).mp hw
    exact (List.mem_cons.mp (h hh.1)).resolve_left hh.2
  induction p with
  | done => exact List.nil_subset _
  | gate g p ih =>
    obtain ⟨hs,sp⟩ := safe
    have hh := List.append_subset.mp hp
    simp only [constantStraight,straightWires,List.append_subset]
    refine ⟨?_,ih sp hh.2⟩
    cases g <;> exact hg _ hs hh.1
  | recordGate i b g p ih =>
    have hh := List.append_subset.mp hp
    exact List.append_subset.mpr ⟨hg g safe.1 hh.1,ih safe.2 hh.2⟩
  | measure w p ih =>
    have hh := List.cons_subset.mp hp
    exact List.cons_subset.mpr ⟨(List.mem_cons.mp hh.1).resolve_left safe.1,ih safe.2 hh.2⟩

theorem straightControlSafe_append {n s m e : Nat} (q : Wire) (p : Straight n s m) (r : Straight n m e) :
    straightControlSafe q (p.append r) ↔ straightControlSafe q p ∧ straightControlSafe q r := by
  induction p <;> simp_all only [Straight.append,straightControlSafe,true_and,and_assoc]

theorem straightControlSafe_castFinish {n s e f : Nat} (q : Wire) (h : e=f) (p : Straight n s e) :
    straightControlSafe q (castFinish h p) ↔ straightControlSafe q p := by subst f; rfl

theorem literalProgram_controlSafe (n start : Nat) (q : Wire) (gs : Circuit)
    (h : ∀ g ∈ gs, constantControlSafe q g) :
    straightControlSafe q (literalProgram (n:=n) (s:=start) gs) := by
  induction gs with
  | nil => trivial
  | cons g gs ih => exact ⟨h g (by simp),ih (fun x hx => h x (by simp [hx]))⟩

theorem recordGates_controlSafe {n s e : Nat} (q : Wire) (i : Fin s) (gs : Circuit) (p : Straight n s e)
    (hg : ∀ g ∈ gs, constantControlSafe q g) (hp : straightControlSafe q p) :
    straightControlSafe q (recordGates i gs p) := by
  induction gs with
  | nil => exact hp
  | cons g gs ih => exact ⟨hg g (by simp),ih (fun x hx => hg x (by simp [hx]))⟩

theorem registerCorrectionProgram_controlSafe {n s e : Nat} (q : Wire) (ws : List Wire)
    (indices : List (Fin s)) (p : Straight n s e) (hw : q ∉ ws) (hp : straightControlSafe q p) :
    straightControlSafe q (registerCorrectionProgram ws indices p) := by
  induction ws generalizing indices with
  | nil => exact hp
  | cons w ws ih =>
    cases indices with
    | nil => exact hp
    | cons i indices =>
      apply recordGates_controlSafe
      · have hne : w ≠ q := by intro he; subst w; exact hw List.mem_cons_self
        simp [pauliZ,constantControlSafe,hne]
      · exact ih indices (fun h => hw (List.mem_cons_of_mem _ h))

theorem deferredCorrectionProgram_controlSafe (n : Nat) (q : Wire) (targets : List Wire)
    (cleanup : Circuit) (cells : List (Circuit × Wire))
    (ht : q ∉ targets) (hc : ∀ g ∈ cleanup, constantControlSafe q g)
    (hcell : ∀ c ∈ cells, (∀ g ∈ c.1, constantControlSafe q g) ∧ c.2 ≠ q)
    (start : Nat) (prior : List (Fin start)) :
    straightControlSafe q (deferredCorrectionProgram n targets cleanup cells start prior) := by
  induction cells generalizing start with
  | nil =>
    apply registerCorrectionProgram_controlSafe _ _ _ _ ht
    apply (straightControlSafe_append _ _ _).mpr
    exact ⟨literalProgram_controlSafe _ _ _ _ hc,
      registerCorrectionProgram_controlSafe _ _ _ _ ht trivial⟩
  | cons c cells ih =>
    simp only [deferredCorrectionProgram,straightControlSafe_castFinish,straightControlSafe_append,straightControlSafe]
    exact ⟨literalProgram_controlSafe _ _ _ _ (hcell c (by simp)).1,
      (hcell c (by simp)).2,ih (fun d hd => hcell d (by simp [hd])) _ _⟩



theorem compareCarryCell_controlSafe (q c r t a d f : Wire) (k last : Bool)
    (h : q ∉ [c,r,t,a,d,f]) :
    ∀ g ∈ gidneyCompareCarryCell q c r t a d f k last, constantControlSafe q g := by
  cases k <;> cases last <;> simp_all [gidneyCompareCarryCell,constantControlSafe,eq_comm]

theorem compareCarryCells_controlSafe (q current spare ancilla flag : Wire)
    (input dirty : List Wire) (constant : List Bool) (support : List Wire) (hq : q ∉ support)
    (hc : current ∈ support) (hs : spare ∈ support) (ha : ancilla ∈ support) (hf : flag ∈ support)
    (hi : input ⊆ support) (hd : dirty ⊆ support) :
    ∀ c ∈ compareCarryCells q current spare ancilla flag input dirty constant,
      (∀ g ∈ c.1, constantControlSafe q g) ∧ c.2 ≠ q := by
  have hneq (w : Wire) (h : w ∈ support) : w ≠ q := fun he => hq (he ▸ h)
  induction input generalizing current spare dirty constant with
  | nil => cases dirty <;> cases constant <;> simp [compareCarryCells,hneq current hc]
  | cons a input ih =>
    cases dirty with
    | nil => simp [compareCarryCells]
    | cons d ds =>
      cases constant with
      | nil => simp [compareCarryCells]
      | cons k ks =>
        simp only [compareCarryCells,List.forall_mem_cons]
        refine ⟨⟨compareCarryCell_controlSafe _ _ _ _ _ _ _ _ _ ?_,hneq current hc⟩,
          ih spare current ds ks hs hc (fun _ h => hi (List.mem_cons_of_mem _ h))
            (fun _ h => hd (List.mem_cons_of_mem _ h))⟩
        intro h
        have hsupp : [current,spare,ancilla,a,d,flag] ⊆ support := by
          simp only [List.cons_subset,List.nil_subset,and_true]
          exact ⟨hc,hs,ha,hi List.mem_cons_self,hd List.mem_cons_self,hf⟩
        exact hq (hsupp h)

theorem compareCarryProgram_controlSafe (n start : Nat) (a d q c r t f : Wire)
    (input dirty : List Wire) (k : Bool) (constant : List Bool) (support : List Wire)
    (hq : q ∉ support) (ha : a ∈ support) (hd : d ∈ support) (hc : c ∈ support)
    (hr : r ∈ support) (ht : t ∈ support) (hf : f ∈ support)
    (hi : input ⊆ support) (hds : dirty ⊆ support) :
    straightControlSafe q (compareCarryProgram n start a d q c r t f input dirty k constant) := by
  have hneq (w : Wire) (h : w ∈ support) : w ≠ q := fun he => hq (he ▸ h)
  simp only [compareCarryProgram,straightControlSafe_append]
  refine ⟨literalProgram_controlSafe _ _ _ _ (compareCarryCell_controlSafe _ _ _ _ _ _ _ _ _ ?_),?_⟩
  · intro h
    have hsupp : [c,r,t,a,d,f] ⊆ support := by
      simp only [List.cons_subset,List.nil_subset,and_true]
      exact ⟨hc,hr,ht,ha,hd,hf⟩
    exact hq (hsupp h)
  · apply deferredCorrectionProgram_controlSafe
    · intro h
      rcases List.mem_cons.mp h with he | h
      · exact hneq d hd he.symm
      · exact hq (hds h)
    · apply controlledConstCarryXor_controlSafe
      intro h
      simp only [List.mem_append,List.mem_cons] at h
      rcases h with (he | he | h) | he | h
      · exact hneq c hc he.symm
      · exact hneq a ha he.symm
      · exact hq (hi h)
      · exact hneq d hd he.symm
      · exact hq (hds h)
    · exact compareCarryCells_controlSafe q r c t f input dirty constant support hq hr hc ht hf hi hds

theorem compareGEProgram_controlSafe (n start : Nat) (input dirty : List Wire) (threshold : Nat)
    (q c r t f : Wire) (support : List Wire) (hq : q ∉ support)
    (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support) (hf : f ∈ support)
    (hi : input ⊆ support) (hd : dirty ⊆ support) :
    straightControlSafe q (compareGEProgram n start input dirty threshold q c r t f).2 := by
  by_cases hz : threshold = 0
  · rw [show compareGEProgram n start input dirty threshold q c r t f = ⟨0,literalProgram [.CX q f]⟩ by simp only [compareGEProgram,hz,ite_true]]
    apply literalProgram_controlSafe
    simp only [List.forall_mem_singleton,constantControlSafe]
    exact fun he => hq (he ▸ hf)
  · by_cases hb : 2^input.length ≤ threshold
    · rw [show compareGEProgram n start input dirty threshold q c r t f = ⟨0,.done⟩ by simp only [compareGEProgram,hz,hb,ite_false,ite_true]]
      trivial
    · rw [show compareGEProgram n start input dirty threshold q c r t f = _ by exact (if_neg hz).trans (if_neg hb)]
      cases input with
      | nil => trivial
      | cons a input =>
        cases dirty with
        | nil => trivial
        | cons d ds =>
          generalize (List.map (2 ^ (a :: input).length - threshold).testBit (List.range (a :: input).length)) = bits
          cases bits with
          | nil => trivial
          | cons k ks =>
            exact compareCarryProgram_controlSafe n start a d q c r t f input ds k ks support hq
              (hi List.mem_cons_self) (hd List.mem_cons_self) hc hr ht hf
              (fun _ h => hi (List.mem_cons_of_mem _ h)) (fun _ h => hd (List.mem_cons_of_mem _ h))

theorem uncontrolledCompareProgram_support (n start : Nat) (input dirty : List Wire) (threshold : Nat)
    (c r t f : Wire) :
    straightWires (uncontrolledCompareProgram n start input dirty threshold c r t f).2 ⊆
      [c,r,t,f] ++ input ++ dirty := by
  let support := [c,r,t,f] ++ input ++ dirty
  let q := gidneyCompareVirtualControl input dirty c r t f
  have hq : q ∉ support := by
    intro h
    have hh := List.le_sum_of_mem h
    change support.sum+1 ≤ support.sum at hh
    exact (Nat.not_succ_le_self _) hh
  have hc : c ∈ support := by simp [support]
  have hr : r ∈ support := by simp [support]
  have ht : t ∈ support := by simp [support]
  have hf : f ∈ support := by simp [support]
  have hi : input ⊆ support := fun _ h => by simp [support,h]
  have hd : dirty ⊆ support := fun _ h => by simp [support,h]
  apply constantStraight_support_erase
  · exact compareGEProgram_controlSafe n start input dirty threshold q c r t f support hq hc hr ht hf hi hd
  · exact compareGEProgram_support n start input dirty threshold q c r t f (q::support)
      List.mem_cons_self (List.mem_cons_of_mem _ hc) (List.mem_cons_of_mem _ hr)
      (List.mem_cons_of_mem _ ht) (List.mem_cons_of_mem _ hf)
      (fun _ h => List.mem_cons_of_mem _ (hi h)) (fun _ h => List.mem_cons_of_mem _ (hd h))



theorem modularAddProgram_support (n start : Nat) (input acc : List Wire) (correction : List Bool)
    (modulus : Nat) (q c r t f : Wire) (support : List Wire)
    (hl : input.length = acc.length) (hk : correction.length = acc.length) (hpos : 0 < acc.length)
    (hq : q ∈ support) (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support) (hf : f ∈ support)
    (hi : input ⊆ support) (ha : acc ⊆ support) :
    straightWires (modularAddProgram n start input acc correction modulus q c r t f).2 ⊆ support := by
  have hsmall : q::c::f::input++acc ⊆ support := by
    simp only [List.append_subset,List.cons_subset]
    exact ⟨⟨hq,hc,hf,hi⟩,ha⟩
  have hfirst := (circuitWires_subset_of_usesOnly (controlledAddCarry_usesOnly input acc q c f)).trans hsmall
  have hcompare cursor := (uncontrolledCompareProgram_support n cursor acc input modulus c r t f).trans
    (show [c,r,t,f]++acc++input ⊆ support by
      simp only [List.append_subset,List.cons_subset,List.nil_subset,and_true]
      exact ⟨⟨⟨hc,hr,ht,hf⟩,ha⟩,hi⟩)
  have htake : acc.length = (input.take (acc.length-1)).length+1 := by
    simp only [List.length_take]; omega
  have hadd cursor := gidneyProgram_support n cursor acc (input.take (acc.length-1)) correction f c r t
    support htake hk hf hc hr ht ha (fun _ h => hi (List.mem_of_mem_take h))
  have hlast : circuitWires (controlledCompareLT acc input q c f) ⊆ support := by
    cases acc with
    | nil => simp at hpos
    | cons a acc =>
      intro w hw
      have h := (controlledCompareLT_wires a acc input q c f w hl.symm).mp hw
      have hsub : q::c::f::(a::acc)++input ⊆ support := by
        simp only [List.append_subset,List.cons_subset]
        exact ⟨⟨hq,hc,hf,(List.cons_subset.mp ha).1,(List.cons_subset.mp ha).2⟩,hi⟩
      exact hsub h
  simp only [modularAddProgram,straightWires_append,literalProgram_support,appendCompiled_support,List.append_subset]
  exact ⟨hfirst,hcompare _,hadd _,hlast⟩



theorem fieldLoadProgram_support_static (field : PointField) (start : Nat) :
    straightWires (fieldLoadProgram field start) ⊆ windowBaseSupport := by
  have hl : ∀ op ∈ fieldLoadOps field, lookupOpWires op ⊆ windowBaseSupport := by
    apply unaryLookupOps_support
    · simp [windowBaseSupport]
    · intro z hz
      simp only [pointLookupPath,List.mem_range'_1] at hz
      simp only [windowBaseSupport,List.mem_append,List.mem_range,List.mem_singleton,List.mem_range'_1]
      (try dsimp only [Wire] at *); omega
    · intro z hz
      have h := (tableAddressTree_mem_index pointLookupAddress 0 1 z).mp hz
      simp only [pointLookupAddress,List.mem_range'_1] at h
      simp only [windowBaseSupport,List.mem_append,List.mem_range,List.mem_singleton,List.mem_range'_1]
      (try dsimp only [Wire] at *); omega
    · intro label q hq
      apply lookupLeafGates_support _ _ _ hq
      intro p hp
      have h := (List.of_mem_zip hp).2
      simp only [List.mem_range'_1] at h
      simp only [windowBaseSupport,List.mem_append,List.mem_range,List.mem_singleton,List.mem_range'_1]
      (try dsimp only [Wire] at *); omega
  simp only [fieldLoadProgram,straightWires_castFinish,lookupProgram_support]
  intro z hz
  obtain ⟨op,hop,hz⟩ := List.mem_flatMap.mp hz
  exact hl op hop hz

theorem fieldLookupAddProgram_support_static (field : PointField) (acc : List Wire)
    (ha : acc ⊆ windowBaseSupport) (hlen : acc.length = 256) (start : Nat) :
    straightWires (fieldLookupAddProgram field acc start).2 ⊆ windowBaseSupport := by
  have had cursor : straightWires (modularAddProgram 32768 cursor (List.range' 7 256) acc
      secp256k1ReductionConstantBits ShorECDLP.p 836 559 560 561 558).2 ⊆ windowBaseSupport := by
    apply modularAddProgram_support
    all_goals try exact ha
    all_goals try simp [hlen,secp256k1ReductionConstantBits,windowBaseSupport]
    · intro w hw
      simp only [List.mem_range'_1] at hw
      simp only [List.mem_append,List.mem_range,List.mem_cons,List.mem_range'_1]
      (try dsimp only [Wire] at *); omega
  simp only [fieldLookupAddProgram,appendCompiled_support,List.append_subset]
  exact ⟨fieldLoadProgram_support_static _ _,had _,fieldLoadProgram_support_static _ _⟩

theorem signedFieldProgram_support_static (field : PointField) (start : Nat) :
    straightWires (signedFieldProgram field start).2 ⊆ windowBaseSupport := by
  have hy : List.range' 580 256 ⊆ windowBaseSupport := by
    intro w hw
    simp only [List.mem_range'_1] at hw
    simp only [windowBaseSupport,List.mem_append,List.mem_range,List.mem_singleton,List.mem_range'_1]
    omega
  simp only [signedFieldProgram,appendCompiled_support,List.append_subset]
  exact ⟨yNegateProgram_support_static _,fieldLookupAddProgram_support_static _ _ hy (by simp) _,yNegateProgram_support_static _⟩

end ShorECDLP.Paper2607_13816.ChallengeMigration
