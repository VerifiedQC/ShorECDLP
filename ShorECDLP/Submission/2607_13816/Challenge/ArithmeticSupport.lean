import ShorECDLP.Submission.«2607_13816».Challenge.BatchSupport
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem registerCorrectionProgram_support {n s e : Nat} (ws support : List Wire)
    (indices : List (Fin s)) (next : Straight n s e) (hw : ws ⊆ support)
    (hn : straightWires next ⊆ support) :
    straightWires (registerCorrectionProgram ws indices next) ⊆ support := by
  induction ws generalizing indices with
  | nil => exact hn
  | cons w ws ih =>
    cases indices with
    | nil => exact hn
    | cons i is =>
      simp only [registerCorrectionProgram,recordGates_support,List.append_subset]
      refine ⟨?_,ih is (fun _ h => hw (List.mem_cons_of_mem _ h))⟩
      simpa [pauliZ,circuitWires,gateWires] using hw List.mem_cons_self

theorem deferredCorrectionProgram_support (n : Nat) (targets support : List Wire)
    (cleanup : Circuit) (cells : List (Circuit × Wire))
    (ht : targets ⊆ support) (hc : circuitWires cleanup ⊆ support)
    (hcell : ∀ c ∈ cells, circuitWires c.1 ⊆ support ∧ c.2 ∈ support)
    (start : Nat) (prior : List (Fin start)) :
    straightWires (deferredCorrectionProgram n targets cleanup cells start prior) ⊆ support := by
  induction cells generalizing start with
  | nil =>
    apply registerCorrectionProgram_support _ _ _ _ ht
    simp only [straightWires_append,literalProgram_support,List.append_subset]
    exact ⟨hc,registerCorrectionProgram_support _ _ _ _ ht (List.nil_subset _)⟩
  | cons c cells ih =>
    simp only [deferredCorrectionProgram,straightWires_castFinish,straightWires_append,
      literalProgram_support,straightWires,List.append_subset,List.cons_subset]
    exact ⟨(hcell c (by simp)).1,(hcell c (by simp)).2,
      ih (fun d hd => hcell d (by simp [hd])) _ _⟩

theorem gidneyAddCarryCell_support (q current spare ancilla input dirty : Wire)
    (constant : Bool) (support : List Wire) (hq : q ∈ support) (hc : current ∈ support)
    (hs : spare ∈ support) (ha : ancilla ∈ support) (hi : input ∈ support) (hd : dirty ∈ support) :
    circuitWires (gidneyAddCarryCell q current spare ancilla input dirty constant) ⊆ support := by
  cases constant <;> simp [gidneyAddCarryCell,circuitWires,gateWires,hq,hc,hs,ha,hi,hd]

theorem gidneyCarryCells_support (q current spare ancilla : Wire)
    (input dirty : List Wire) (constant : List Bool) (support : List Wire)
    (hq : q ∈ support) (hc : current ∈ support) (hs : spare ∈ support) (ha : ancilla ∈ support)
    (hi : input ⊆ support) (hd : dirty ⊆ support) :
    ∀ c ∈ gidneyCarryCells q current spare ancilla input dirty constant,
      circuitWires c.1 ⊆ support ∧ c.2 ∈ support := by
  induction input generalizing current spare dirty constant with
  | nil => simp [gidneyCarryCells]
  | cons a input ih =>
    have ha' := hi List.mem_cons_self
    have hi' : input ⊆ support := fun _ h => hi (List.mem_cons_of_mem _ h)
    cases constant with
    | nil => cases input <;> cases dirty <;> simp [gidneyCarryCells]
    | cons k ks =>
      cases dirty with
      | nil =>
        cases input with
        | nil =>
          cases ks with
          | nil => cases k <;> simp [gidneyCarryCells,circuitWires,gateWires,hq,hc,ha']
          | cons _ _ => simp [gidneyCarryCells]
        | cons _ _ => simp [gidneyCarryCells]
      | cons d ds =>
        simp only [gidneyCarryCells,List.forall_mem_cons]
        exact ⟨⟨gidneyAddCarryCell_support _ _ _ _ _ _ _ _ hq hc hs ha ha' (hd List.mem_cons_self),hc⟩,
          ih spare current ds ks hs hc hi' (fun _ h => hd (List.mem_cons_of_mem _ h))⟩

theorem gidneyAddCleanup_support (input dirty : List Wire) (constant : List Bool)
    (q carry : Wire) (support : List Wire) (hq : q ∈ support) (hc : carry ∈ support)
    (hi : input ⊆ support) (hd : dirty ⊆ support) :
    circuitWires (gidneyAddCleanup input dirty constant q carry) ⊆ support := by
  have hf : circuitWires (gidneyFlipWord input) ⊆ support := by
    intro w hw
    obtain ⟨g,hg,hw⟩ := List.mem_flatMap.mp hw
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hg
    have he : w = v := by simpa only [gateWires,List.mem_singleton] using hw
    exact he ▸ hi hv
  have hm := circuitWires_subset_of_usesOnly (controlledConstCarryXor_usesOnly
    (input.take dirty.length) dirty (constant.take dirty.length) q carry)
  have hm' : circuitWires (controlledConstCarryXor (input.take dirty.length) dirty
      (constant.take dirty.length) q carry) ⊆ support := by
    apply hm.trans
    intro w hw
    simp only [List.mem_append,List.mem_cons] at hw
    rcases hw with (rfl | rfl | hw) | hw
    · exact hq
    · exact hc
    · exact hi (List.mem_of_mem_take hw)
    · exact hd hw
  simpa only [gidneyAddCleanup,circuitWires,List.flatMap_append,List.append_subset] using
    And.intro (And.intro hf hm') hf



theorem gidneyNontrivialProgram_support (n start : Nat) (a d q carry spare ancilla : Wire)
    (input dirty : List Wire) (k : Bool) (constant : List Bool) (support : List Wire)
    (ha : a ∈ support) (hd : d ∈ support) (hq : q ∈ support) (hc : carry ∈ support)
    (hs : spare ∈ support) (ht : ancilla ∈ support)
    (hi : input ⊆ support) (hds : dirty ⊆ support) :
    straightWires (gidneyNontrivialProgram n start a d q carry spare ancilla input dirty k constant) ⊆ support := by
  simp only [gidneyNontrivialProgram,straightWires_append,literalProgram_support,List.append_subset]
  refine ⟨gidneyAddCarryCell_support _ _ _ _ _ _ _ _ hq hc hs ht ha hd,?_⟩
  apply deferredCorrectionProgram_support
  · exact List.cons_subset.mpr ⟨hd,hds⟩
  · exact gidneyAddCleanup_support _ _ _ _ _ _ hq hc
      (List.cons_subset.mpr ⟨ha,hi⟩) (List.cons_subset.mpr ⟨hd,hds⟩)
  · exact gidneyCarryCells_support _ _ _ _ _ _ _ _ hq hs hc ht hi hds

theorem gidneyProgram_support (n start : Nat) (input dirty : List Wire) (constant : List Bool)
    (q carry spare ancilla : Wire) (support : List Wire)
    (hlen : input.length = dirty.length+1) (hk : constant.length = input.length)
    (hq : q ∈ support) (hc : carry ∈ support) (hs : spare ∈ support) (ht : ancilla ∈ support)
    (hi : input ⊆ support) (hd : dirty ⊆ support) :
    straightWires (gidneyProgram n start input dirty constant q carry spare ancilla).2 ⊆ support := by
  by_cases hz : constant.all (fun k => !k) = true
  · rw [show gidneyProgram n start input dirty constant q carry spare ancilla = ⟨0,.done⟩ by simp only [gidneyProgram,hz,ite_true]]
    exact List.nil_subset _
  · rw [show gidneyProgram n start input dirty constant q carry spare ancilla = _ by exact if_neg hz]
    cases input with
    | nil => simp at hlen
    | cons a input =>
      cases constant with
      | nil => simp at hk
      | cons k ks =>
        cases dirty with
        | nil =>
          have he : input=[] := List.eq_nil_of_length_eq_zero (by simp_all)
          have he' : ks=[] := List.eq_nil_of_length_eq_zero (by simp_all)
          subst input; subst ks
          have ha := hi List.mem_cons_self
          cases k <;> simp [literalProgram_support,circuitWires,gateWires,hq,ha]
        | cons d ds =>
          have h := gidneyNontrivialProgram_support n start a d q carry spare ancilla input ds k ks support
            (hi List.mem_cons_self) (hd List.mem_cons_self) hq hc hs ht
            (fun _ h => hi (List.mem_cons_of_mem _ h)) (fun _ h => hd (List.mem_cons_of_mem _ h))
          cases input with
          | nil => simp at hlen
          | cons b bs => exact h



theorem compareCarryCell_support (q current spare ancilla input dirty flag : Wire)
    (constant last : Bool) (support : List Wire) (hq : q ∈ support) (hc : current ∈ support)
    (hs : spare ∈ support) (ha : ancilla ∈ support) (hi : input ∈ support)
    (hd : dirty ∈ support) (hf : flag ∈ support) :
    circuitWires (gidneyCompareCarryCell q current spare ancilla input dirty flag constant last) ⊆ support := by
  cases constant <;> cases last <;>
    simp [gidneyCompareCarryCell,circuitWires,gateWires,hq,hc,hs,ha,hi,hd,hf]

theorem compareCarryCells_support (q current spare ancilla flag : Wire)
    (input dirty : List Wire) (constant : List Bool) (support : List Wire)
    (hq : q ∈ support) (hc : current ∈ support) (hs : spare ∈ support)
    (ha : ancilla ∈ support) (hf : flag ∈ support)
    (hi : input ⊆ support) (hd : dirty ⊆ support) :
    ∀ c ∈ compareCarryCells q current spare ancilla flag input dirty constant,
      circuitWires c.1 ⊆ support ∧ c.2 ∈ support := by
  induction input generalizing current spare dirty constant with
  | nil => cases dirty <;> cases constant <;> simp [compareCarryCells,circuitWires,hc]
  | cons a input ih =>
    cases dirty with
    | nil => simp [compareCarryCells]
    | cons d ds =>
      cases constant with
      | nil => simp [compareCarryCells]
      | cons k ks =>
        simp only [compareCarryCells,List.forall_mem_cons]
        exact ⟨⟨compareCarryCell_support _ _ _ _ _ _ _ _ _ _ hq hc hs ha
          (hi List.mem_cons_self) (hd List.mem_cons_self) hf,hc⟩,
          ih spare current ds ks hs hc (fun _ h => hi (List.mem_cons_of_mem _ h))
            (fun _ h => hd (List.mem_cons_of_mem _ h))⟩

theorem carryXor_support (input dirty : List Wire) (constant : List Bool)
    (q carry : Wire) (support : List Wire) (hq : q ∈ support) (hc : carry ∈ support)
    (hi : input ⊆ support) (hd : dirty ⊆ support) :
    circuitWires (controlledConstCarryXor input dirty constant q carry) ⊆ support := by
  apply (circuitWires_subset_of_usesOnly (controlledConstCarryXor_usesOnly _ _ _ _ _)).trans
  intro w hw
  simp only [List.mem_append,List.mem_cons] at hw
  rcases hw with (rfl | rfl | hw) | hw
  · exact hq
  · exact hc
  · exact hi hw
  · exact hd hw

theorem compareCarryProgram_support (n start : Nat) (a d q carry spare ancilla flag : Wire)
    (input dirty : List Wire) (k : Bool) (constant : List Bool) (support : List Wire)
    (ha : a ∈ support) (hd : d ∈ support) (hq : q ∈ support) (hc : carry ∈ support)
    (hs : spare ∈ support) (ht : ancilla ∈ support) (hf : flag ∈ support)
    (hi : input ⊆ support) (hds : dirty ⊆ support) :
    straightWires (compareCarryProgram n start a d q carry spare ancilla flag input dirty k constant) ⊆ support := by
  simp only [compareCarryProgram,straightWires_append,literalProgram_support,List.append_subset]
  refine ⟨compareCarryCell_support _ _ _ _ _ _ _ _ _ _ hq hc hs ht ha hd hf,?_⟩
  apply deferredCorrectionProgram_support
  · exact List.cons_subset.mpr ⟨hd,hds⟩
  · exact carryXor_support _ _ _ _ _ _ hq hc
      (List.cons_subset.mpr ⟨ha,hi⟩) (List.cons_subset.mpr ⟨hd,hds⟩)
  · exact compareCarryCells_support _ _ _ _ _ _ _ _ _ hq hs hc ht hf hi hds

theorem compareGEProgram_support (n start : Nat) (input dirty : List Wire) (threshold : Nat)
    (q carry spare ancilla flag : Wire) (support : List Wire)
    (hq : q ∈ support) (hc : carry ∈ support) (hs : spare ∈ support)
    (ht : ancilla ∈ support) (hf : flag ∈ support)
    (hi : input ⊆ support) (hd : dirty ⊆ support) :
    straightWires (compareGEProgram n start input dirty threshold q carry spare ancilla flag).2 ⊆ support := by
  by_cases hz : threshold = 0
  · rw [show compareGEProgram n start input dirty threshold q carry spare ancilla flag = ⟨0,literalProgram [.CX q flag]⟩ by simp only [compareGEProgram,hz,ite_true]]
    simp [literalProgram_support,circuitWires,gateWires,hq,hf]
  · by_cases hb : 2^input.length ≤ threshold
    · rw [show compareGEProgram n start input dirty threshold q carry spare ancilla flag = ⟨0,.done⟩ by simp only [compareGEProgram,hz,hb,ite_false,ite_true]]
      exact List.nil_subset _
    · rw [show compareGEProgram n start input dirty threshold q carry spare ancilla flag = _ by exact (if_neg hz).trans (if_neg hb)]
      cases input with
      | nil => exact List.nil_subset _
      | cons a input =>
        cases dirty with
        | nil => exact List.nil_subset _
        | cons d ds =>
          generalize (List.map (2 ^ (a :: input).length - threshold).testBit (List.range (a :: input).length)) = bits
          cases bits with
          | nil => exact List.nil_subset _
          | cons k ks =>
            exact compareCarryProgram_support _ _ _ _ _ _ _ _ _ _ _ _ _ _
              (hi List.mem_cons_self) (hd List.mem_cons_self) hq hc hs ht hf
              (fun _ h => hi (List.mem_cons_of_mem _ h)) (fun _ h => hd (List.mem_cons_of_mem _ h))



theorem prependCompiled_support {n start : Nat} (gs : Circuit)
    (p : (count : Nat) × Straight n start (start+count)) :
    straightWires (prependCompiled gs p).2 = circuitWires gs ++ straightWires p.2 := by
  simp only [prependCompiled,straightWires_append,literalProgram_support]

theorem modularNegateProgram_support (n start : Nat) (target dirty : List Wire) (modulus : List Bool)
    (q c r t f : Wire) (support : List Wire)
    (hd : target.length = dirty.length) (hk : modulus.length = target.length) (hpos : 0 < target.length)
    (hq : q ∈ support) (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support) (hf : f ∈ support)
    (hx : target ⊆ support) (hy : dirty ⊆ support) :
    straightWires (modularNegateProgram n start target dirty modulus q c r t f).2 ⊆ support := by
  have htake : target.length = (dirty.take (target.length-1)).length+1 := by
    simp only [List.length_take]; omega
  have hyt : dirty.take (target.length-1) ⊆ support := fun _ h => hy (List.mem_of_mem_take h)
  have htest cursor := compareGEProgram_support n cursor target dirty 1 q c r t f support hq hc hr ht hf hx hy
  have hinc cursor := gidneyProgram_support n cursor target (dirty.take (target.length-1))
    ((List.range target.length).map (Nat.testBit 1)) q c r t support htake (by simp) hq hc hr ht hx hyt
  have hadd cursor := gidneyProgram_support n cursor target (dirty.take (target.length-1))
    modulus f c r t support htake hk hf hc hr ht hx hyt
  have hcomp : circuitWires (controlledComplement target q) ⊆ support := by
    intro w hw
    obtain ⟨g,hg,hw⟩ := List.mem_flatMap.mp hw
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hg
    have hv' := hx hv
    rcases (show w = q ∨ w = v by simpa [gateWires] using hw) with rfl | rfl
    · exact hq
    · exact hv'
  simp only [modularNegateProgram,appendCompiled_support,prependCompiled_support,List.append_subset]
  exact ⟨htest _,hcomp,hinc _,hadd _,htest _⟩

theorem negativeNegateProgram_support (n start : Nat) (target dirty : List Wire) (modulus : List Bool)
    (q c r t f : Wire) (support : List Wire)
    (hd : target.length = dirty.length) (hk : modulus.length = target.length) (hpos : 0 < target.length)
    (hq : q ∈ support) (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support) (hf : f ∈ support)
    (hx : target ⊆ support) (hy : dirty ⊆ support) :
    straightWires (negativeNegateProgram n start target dirty modulus q c r t f).2 ⊆ support := by
  have hp := modularNegateProgram_support n start target dirty modulus q c r t f support hd hk hpos hq hc hr ht hf hx hy
  have hq' : circuitWires [.X q] ⊆ support := by simpa [circuitWires,gateWires] using hq
  simp only [negativeNegateProgram,prependCompiled_support,appendCompiled_support,literalProgram_support,List.append_subset]
  exact ⟨hq',hp,hq'⟩

/-- Active source bank before relocation; gap 837 is not an allocated wire. -/
def windowBaseSupport : List Wire := List.range 837 ++ [838] ++ List.range' 839 16

theorem yNegateProgram_support_static (start : Nat) :
    straightWires (yNegateProgram start).2 ⊆ windowBaseSupport := by
  apply negativeNegateProgram_support
  all_goals try simp [windowBaseSupport]
  all_goals intro w hw
  all_goals simp only [List.mem_append,List.mem_cons,List.mem_range'_1,List.mem_range] at hw ⊢
  all_goals (try dsimp only [Wire] at *); omega



theorem windowBaseSupport_relocated (z : Wire) (hz : z ∈ windowBaseSupport) :
    windowAddressPerm 855 (by decide) z ∈ resetWires := by
  change windowAddressSwap 855 z ∈ resetWires
  simp only [windowBaseSupport,List.mem_append,List.mem_range,List.mem_singleton,List.mem_range'_1] at hz
  simp only [resetWires,List.mem_append,List.mem_range,List.mem_singleton,List.mem_range'_1]
  unfold windowAddressSwap
  split_ifs <;> dsimp only [Wire] at * <;> omega

theorem sharedYNegateProgram_support_static (w : OddWindow) (start : Nat) :
    (straightWires (sharedYNegateProgram w start).2).map (windowAddressPerm 855 (by decide))
      ⊆ batchedResetWires := by
  simp only [sharedYNegateProgram,reindexCompiled_support]
  intro z hz
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hz
  exact List.mem_append_left _ (List.mem_append_left _
    (windowBaseSupport_relocated v (yNegateProgram_support_static start hv)))

end ShorECDLP.Paper2607_13816.ChallengeMigration
