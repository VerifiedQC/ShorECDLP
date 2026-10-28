import ShorECDLP.Submission.«2607_13816».Challenge.StructuralSupport
import ShorECDLP.Submission.«2607_13816».Challenge.BatchTemplate
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

/-- Turn the source gate-by-gate support judgment into the wire collector used
by the challenge. No semantic equivalence is used to infer support. -/
theorem circuitWires_subset_of_usesOnly {support : List Wire} {gs : Circuit}
    (h : PaperCircuitUsesOnly support gs) : circuitWires gs ⊆ support := by
  intro w hw
  obtain ⟨g,hg,hw⟩ := List.mem_flatMap.mp hw
  exact h g hg w hw

theorem registerEqualCircuit_support (cells : List (Wire × Wire)) (flag : Wire)
    (scratch support : List Wire) (hf : flag ∈ support) (hs : scratch ⊆ support)
    (hc : ∀ c ∈ cells, c.1 ∈ support ∧ c.2 ∈ support) :
    circuitWires (registerEqualCircuit cells flag scratch) ⊆ support := by
  have hx : circuitWires (xorWordCircuit cells) ⊆ support := by
    intro w hw
    obtain ⟨g,hg,hw⟩ := List.mem_flatMap.mp hw
    obtain ⟨c,hc',rfl⟩ := List.mem_map.mp hg
    simp only [gateWires,List.mem_cons,List.mem_nil_iff,or_false] at hw
    rcases hw with rfl | rfl
    · exact (hc c hc').1
    · exact (hc c hc').2
  have he : circuitWires (computeEqConst (cells.map Prod.snd) 0 flag scratch) ⊆ support := by
    apply (circuitWires_subset_of_usesOnly (computeEqConst_usesOnly _ _ _ _)).trans
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨c,hc',rfl⟩ := List.mem_map.mp hw
      exact (hc c hc').2
    · rcases List.mem_cons.mp hw with rfl | hw
      · exact hf
      · exact hs hw
  simpa only [registerEqualCircuit,circuitWires,List.flatMap_append,List.append_subset] using
    And.intro (And.intro hx he) hx

theorem endpointTranspositionCircuit_support {n : Nat} (a b target : Fin n → Wire)
    (flag : Wire) (scratch support : List Wire)
    (ha : ∀ i, a i ∈ support) (hb : ∀ i, b i ∈ support) (ht : ∀ i, target i ∈ support)
    (hf : flag ∈ support) (hs : scratch ⊆ support) :
    circuitWires (endpointTranspositionCircuit a b target flag scratch) ⊆ support := by
  have he (r : Fin n → Wire) (hr : ∀ i, r i ∈ support) :
      circuitWires (registerEqualCircuit (equalityCells r target) flag scratch) ⊆ support := by
    apply registerEqualCircuit_support _ _ _ _ hf hs
    intro c hc
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
    exact ⟨hr i,ht i⟩
  have hu : circuitWires (endpointWordCircuit flag (endpointUpdateCells a b target)) ⊆ support := by
    intro w hw
    obtain ⟨g,hg,hw⟩ := List.mem_flatMap.mp hw
    obtain ⟨c,hc,hg⟩ := List.mem_flatMap.mp hg
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
    simp only [endpointBitCircuit,List.mem_cons,List.mem_nil_iff,or_false] at hg
    rcases hg with rfl | rfl
    all_goals simp only [gateWires,List.mem_cons,List.mem_nil_iff,or_false] at hw
    all_goals rcases hw with rfl | rfl | rfl
    all_goals first | exact hf | exact ha i | exact hb i | exact ht i
  have he' : circuitWires (endpointTests a b target flag scratch) ⊆ support := by
    simpa only [endpointTests,circuitWires,List.flatMap_append,List.append_subset] using And.intro (he a ha) (he b hb)
  simpa only [endpointTranspositionCircuit,circuitWires,List.flatMap_append,List.append_subset] using
    And.intro (And.intro he' hu) he'


/-- Static support of a constant-controlled leaf, including disabled slots. -/
theorem endpointSelectGates_support {n : Nat} (control : Wire)
    (ports : List (Wire × EndpointBit n)) (support : List Wire)
    (hq : control ∈ support) (hp : ∀ p ∈ ports, p.1 ∈ support) :
    (endpointSelectGates control ports).flatMap templateGateWires ⊆ support := by
  intro w hw
  obtain ⟨g,hg,hw⟩ := List.mem_flatMap.mp hw
  obtain ⟨p,hp',hg⟩ := List.mem_flatMap.mp hg
  have hpw := hp p hp'
  rcases p with ⟨port,bit⟩
  cases bit with
  | inl bit =>
    cases bit with
    | false => simp [endpointSelectGate] at hg
    | true =>
      simp only [endpointSelectGate,List.mem_singleton] at hg
      subst g
      rcases (show w = control ∨ w = port by simpa [templateGateWires,gateWires] using hw) with rfl | rfl
      · exact hq
      · exact hpw
  | inr bit =>
    simp only [endpointSelectGate,List.mem_singleton] at hg
    subst g
    rcases (show w = control ∨ w = port by simpa [templateGateWires,gateWires] using hw) with rfl | rfl
    · exact hq
    · exact hpw

theorem batchLeaf_support {n : Nat} (row : Fin n) (base control : Wire)
    (selection : List (Fin 8 × Fin 5)) (support : List Wire)
    (hq : control ∈ support) (hb : List.range' base 2565 ⊆ support) :
    (batchLeaf row base control selection).flatMap templateGateWires ⊆ support := by
  simp only [batchLeaf,List.flatMap_append,List.append_subset]
  constructor
  · apply endpointSelectGates_support _ _ _ hq
    intro p hp
    exact hb (List.mem_range'_1.mpr (batchPorts_bounds row base p.1 selection (List.mem_map.mpr ⟨p,hp,rfl⟩)))
  · intro w hw
    simp only [List.flatMap_map,List.mem_flatMap] at hw
    obtain ⟨p,hp,hw⟩ := hw
    have hpw := hb (List.mem_range'_1.mpr (batchTags_bounds base p selection hp))
    rcases (show w = control ∨ w = p by simpa [templateGateWires,gateWires] using hw) with rfl | rfl
    · exact hq
    · exact hpw

theorem batchOpCircuit_support (base : Wire) (source : Fin 4) (target : Fin 6) :
    circuitWires (batchOpCircuit base source target) ⊆ List.range' base 3590 := by
  apply endpointTranspositionCircuit_support
  all_goals simp only [List.mem_range'_1,batchWord,batchFlag,batchScratch]
  all_goals try (intro i; have := i.isLt; dsimp only [Wire] at *; omega)
  · dsimp only [Wire] at *; omega
  · intro w hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    have := i.isLt
    simp only [List.mem_range'_1]
    dsimp only [Wire] at *; omega

theorem batchOps_support {n : Nat} (rows : Nat → Fin n) (base : Wire)
    (tree : UnaryActionTree) (control : Wire) (paths support : List Wire)
    (hc : control ∈ support) (hp : paths ⊆ support) (ht : tree.indexWires ⊆ support)
    (hb : List.range' base 3590 ⊆ support) (ops : List BatchOp) :
    ∀ op ∈ batchOps rows base tree control paths ops, lookupOpWires op ⊆ support := by
  have hsmall : List.range' base 2565 ⊆ support := by
    intro w hw
    apply hb
    simp only [List.mem_range'_1] at hw ⊢
    omega
  induction ops with
  | nil => simp [batchOps]
  | cons op ops ih =>
    cases op with
    | query sources target =>
      simp only [batchOps,List.forall_mem_append]
      exact ⟨unaryLookupOps_support _ _ _ _ _ hc hp ht
        (fun l q hq => batchLeaf_support _ _ _ _ _ hq hsmall),ih⟩
    | swap source target =>
      simp only [batchOps,List.forall_mem_cons,ordinaryOp_support]
      exact ⟨(batchOpCircuit_support base source target).trans hb,ih⟩

theorem batchedEndpointProgram_support {n : Nat} (rows : Nat → Fin n) (base : Wire)
    (tree : UnaryActionTree) (control : Wire) (paths support : List Wire)
    (hc : control ∈ support) (hp : paths ⊆ support) (ht : tree.indexWires ⊆ support)
    (hb : List.range' base 3590 ⊆ support) (start : Nat) :
    straightWires (batchedEndpointProgram rows base tree control paths start).2 ⊆ support := by
  simp only [batchedEndpointProgram,lookupProgram_support]
  intro w hw
  obtain ⟨op,hop,hw⟩ := List.mem_flatMap.mp hw
  exact batchOps_support rows base tree control paths support hc hp ht hb batchSchedule op hop hw


/-- Component allocation before the data-bank permutation. -/
def batchRawSupport : List Wire :=
  836 :: pointLookupPath ++ pointLookupAddress ++ List.range' 1024 3590

theorem batchWindow_support_raw (w : OddWindow) (start : Nat) :
    straightWires (batchedEndpointProgram (batchWindowRows w) 1024
      batchWindowTree 836 pointLookupPath start).2 ⊆ batchRawSupport := by
  apply batchedEndpointProgram_support
  · simp [batchRawSupport]
  · intro z hz; simp [batchRawSupport,hz]
  · intro z hz
    have h := (tableAddressTree_mem_index pointLookupAddress 0 1 z).mp hz
    simp [batchRawSupport,h]
  · intro z hz; simp [batchRawSupport,hz]

/-- Both real wire permutations place the complete correction block inside the
same reset allocation. In particular the temporary sixth word is replaced by
accumulator ports; it is not counted as an additional resident word. -/
theorem batchRawSupport_placed (z : Wire) (hz : z ∈ batchRawSupport) :
    windowAddressPerm 855 (by decide) (batchPlacement z) ∈ batchedResetWires := by
  change windowAddressSwap 855 (batchPlacementFn z) ∈ batchedResetWires
  simp only [batchRawSupport,pointLookupPath,pointLookupAddress,List.mem_cons,
    List.mem_append,List.mem_range'_1] at hz
  simp only [batchedResetWires,resetWires,List.mem_append,List.mem_range,
    List.mem_singleton,List.mem_range'_1]
  unfold batchPlacementFn windowAddressSwap
  split_ifs <;> dsimp only [Wire] at * <;> omega

attribute [local irreducible] batchedEndpointProgram

theorem placedBatchProgram_support_static (w : OddWindow) (start : Nat) :
    (straightWires (placedBatchProgram w start).2).map (windowAddressPerm 855 (by decide))
      ⊆ batchedResetWires := by
  simp only [placedBatchProgram,relabelCompiled_support,List.map_map]
  intro z hz
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hz
  exact batchRawSupport_placed v (batchWindow_support_raw w start hv)

end ShorECDLP.Paper2607_13816.ChallengeMigration
