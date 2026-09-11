import ShorECDLP.Submission.«2607_13816».Window.LookupArithmetic
import ShorECDLP.Submission.«2607_13816».Arithmetic.PointStages
import ShorECDLP.Submission.«2607_13816».Arithmetic.HornerSupport
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section
/-- Persistent address bank outside the 839-wire point core. -/
def pointLookupAddress : List Wire := List.range' 839 16
/-- Decoder path borrows clean point work and is cleared before the arithmetic core resumes. -/
def pointLookupPath : List Wire := List.range' 519 16

def fig14LookupX (table : Nat → Nat) : AdaptiveCircuit :=
  lookupModularAddProgram table pointLookupAddress pointLookupPath
    (List.range' 7 256) (List.range' 263 256) secp256k1ReductionConstantBits
    ShorECDLP.p 836 559 560 561 558

def fig14LookupXState (table : Nat → Nat) : BasisState → BasisState :=
  lookupModularAddState table pointLookupAddress (List.range' 7 256) (List.range' 263 256)
    secp256k1ReductionConstantBits ShorECDLP.p 836 559 558

private theorem point_lookup_valid (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s)
    (hq : s 836=true) :
    LookupModularValid pointLookupPath (List.range' 7 256) (List.range' 263 256)
      ShorECDLP.p 836 559 560 561 558 s := by
  refine ⟨?_,?_,hq,?_,?_,?_,?_,hs.2.2.1⟩
  · intro w hw
    apply hs.1 w
    simp [pointLookupPath] at hw ⊢
    omega
  · intro w hw
    apply hs.1 w
    simp at hw ⊢
    omega
  · exact hs.1 559 (by decide +kernel)
  · exact hs.1 560 (by decide +kernel)
  · exact hs.1 561 (by decide +kernel)
  · exact hs.1 558 (by decide +kernel)

private theorem word_frame_equal (acc : List Wire) (s left right : BasisState)
    (hword : boolWordToNat (wireValues acc left)=boolWordToNat (wireValues acc right))
    (hl : ∀ w, w∉acc → left w=s w) (hr : ∀ w, w∉acc → right w=s w) : left=right := by
  have he := boolWordToNat_injective_of_length (by simp [wireValues]) hword
  funext w
  by_cases hw : w∈acc
  · exact List.map_inj_left.mp he w hw
  · rw [hl w hw,hr w hw]

theorem fig14LookupXState_eq (table : Nat → Nat) (hv : ∀ label, table label<ShorECDLP.p)
    (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) (hq : s 836=true) :
    fig14LookupXState table s=fig14ConstantXState (table (tableAddressValue pointLookupAddress s)) s := by
  have h := lookupModularAddState_correct table pointLookupAddress pointLookupPath
    (List.range' 7 256) (List.range' 263 256) secp256k1ReductionConstantBits ShorECDLP.p
    836 559 560 561 558 (by apply List.disjoint_left.mpr; intro w hw ht; simp only [pointLookupAddress,pointLookupPath,List.mem_cons,List.mem_append,List.mem_range'] at hw ht; rcases hw with (rfl | ⟨i,hi,hwi⟩) | ⟨i,hi,hwi⟩ <;> obtain ⟨j,hj,hwj⟩ := ht <;> omega) (by apply List.disjoint_left.mpr; intro w hw ht; simp only [pointLookupAddress,List.mem_range'] at hw ht; omega) (by simp)
    (by simp [secp256k1ReductionConstantBits]) (by decide +kernel) (by decide +kernel)
    (by rw [secp256k1ReductionConstant_value]; decide +kernel) hv s (point_lookup_valid s hs hq)
  have hc := fig14ConstantXState_correct (table (tableAddressValue pointLookupAddress s)) (hv _) s hs
  exact word_frame_equal (List.range' 263 256) s _ _ (h.1.trans hc.1.symm) h.2 hc.2

def fig14LookupY (table : Nat → Nat) : AdaptiveCircuit :=
  lookupModularAddProgram table pointLookupAddress pointLookupPath
    (List.range' 7 256) (List.range' 580 256) secp256k1ReductionConstantBits
    ShorECDLP.p 836 559 560 561 558

def fig14LookupYState (table : Nat → Nat) : BasisState → BasisState :=
  lookupModularAddState table pointLookupAddress (List.range' 7 256) (List.range' 580 256)
    secp256k1ReductionConstantBits ShorECDLP.p 836 559 558

private theorem point_lookup_valid_Y (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s)
    (hq : s 836=true) :
    LookupModularValid pointLookupPath (List.range' 7 256) (List.range' 580 256)
      ShorECDLP.p 836 559 560 561 558 s := by
  have h := point_lookup_valid s hs hq
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,h.2.2.2.2.2.2.1,hs.2.2.2⟩

theorem fig14LookupYState_eq (table : Nat → Nat) (hv : ∀ label, table label<ShorECDLP.p)
    (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) (hq : s 836=true) :
    fig14LookupYState table s=fig14ControlledConstantYState (table (tableAddressValue pointLookupAddress s)) s := by
  have h := lookupModularAddState_correct table pointLookupAddress pointLookupPath
    (List.range' 7 256) (List.range' 580 256) secp256k1ReductionConstantBits ShorECDLP.p
    836 559 560 561 558 (by apply List.disjoint_left.mpr; intro w hw ht; simp only [pointLookupAddress,pointLookupPath,List.mem_cons,List.mem_append,List.mem_range'] at hw ht; rcases hw with (rfl | ⟨i,hi,hwi⟩) | ⟨i,hi,hwi⟩ <;> obtain ⟨j,hj,hwj⟩ := ht <;> omega) (by apply List.disjoint_left.mpr; intro w hw ht; simp only [pointLookupAddress,List.mem_range'] at hw ht; omega) (by simp)
    (by simp [secp256k1ReductionConstantBits]) (by decide +kernel) (by decide +kernel)
    (by rw [secp256k1ReductionConstant_value]; decide +kernel) hv s (point_lookup_valid_Y s hs hq)
  have hc := fig14ControlledConstantYState_correct (table (tableAddressValue pointLookupAddress s)) (hv _) s hs
  have hc' : boolWordToNat (wireValues (List.range' 580 256)
      (fig14ControlledConstantYState (table (tableAddressValue pointLookupAddress s)) s))=
      (boolWordToNat (wireValues (List.range' 580 256) s)+table (tableAddressValue pointLookupAddress s))%ShorECDLP.p := by
    simpa only [hq,if_true] using hc.1
  exact word_frame_equal (List.range' 580 256) s _ _ (h.1.trans hc'.symm) h.2 hc.2

/-- Canonical point-core inputs with the lookup root held enabled. -/
def PointLookupValid (s : BasisState) : Prop := Secp256k1ZeroAllowedInputValid s ∧ s 836=true

private theorem point_lookup_strengthen {program : AdaptiveCircuit}
    {ideal : Quantum.State →ₗ[ℂ] Quantum.State} {Valid : BasisState → Prop}
    (h : CoherentlyImplementsOn program ideal Valid) (hsub : ∀ s, PointLookupValid s → Valid s) :
    CoherentlyImplementsOn program ideal PointLookupValid := by
  obtain ⟨cs,ha,hm⟩ := h
  exact ⟨cs,ha.imp (fun b c hb s hs => hb s (hsub s hs)),hm⟩

theorem fig14LookupX_coherent (table : Nat → Nat) (hv : ∀ label, table label<ShorECDLP.p) :
    CoherentlyImplementsOn (fig14LookupX table)
      (Finsupp.lmapDomain ℂ ℂ (fig14LookupXState table)) PointLookupValid := by
  apply point_lookup_strengthen
    (lookupModularAddProgram_coherent table pointLookupAddress pointLookupPath
      (List.range' 7 256) (List.range' 263 256) secp256k1ReductionConstantBits ShorECDLP.p
      836 559 560 561 558 (by decide +kernel) (by decide +kernel) (by apply List.disjoint_left.mpr; intro w hw ht; simp only [pointLookupAddress,pointLookupPath,List.mem_cons,List.mem_append,List.mem_range'] at hw ht; rcases hw with (rfl | ⟨i,hi,hwi⟩) | ⟨i,hi,hwi⟩ <;> obtain ⟨j,hj,hwj⟩ := ht <;> omega)
      (by apply List.disjoint_left.mpr; intro w hw ht; simp only [pointLookupPath,List.mem_range'] at hw ht; omega) (by simp) (by decide +kernel) (by simp [secp256k1ReductionConstantBits])
      (by decide +kernel) ShorECDLP.Secp256k1.p_prime.pos (by decide +kernel)
      (by rw [secp256k1ReductionConstant_value]; decide +kernel) hv)
  exact fun s hs => point_lookup_valid s hs.1 hs.2

theorem fig14LookupY_coherent (table : Nat → Nat) (hv : ∀ label, table label<ShorECDLP.p) :
    CoherentlyImplementsOn (fig14LookupY table)
      (Finsupp.lmapDomain ℂ ℂ (fig14LookupYState table)) PointLookupValid := by
  apply point_lookup_strengthen
    (lookupModularAddProgram_coherent table pointLookupAddress pointLookupPath
      (List.range' 7 256) (List.range' 580 256) secp256k1ReductionConstantBits ShorECDLP.p
      836 559 560 561 558 (by decide +kernel) (by decide +kernel) (by apply List.disjoint_left.mpr; intro w hw ht; simp only [pointLookupAddress,pointLookupPath,List.mem_cons,List.mem_append,List.mem_range'] at hw ht; rcases hw with (rfl | ⟨i,hi,hwi⟩) | ⟨i,hi,hwi⟩ <;> obtain ⟨j,hj,hwj⟩ := ht <;> omega)
      (by apply List.disjoint_left.mpr; intro w hw ht; simp only [pointLookupPath,List.mem_range'] at hw ht; omega) (by simp) (by decide +kernel) (by simp [secp256k1ReductionConstantBits])
      (by decide +kernel) ShorECDLP.Secp256k1.p_prime.pos (by decide +kernel)
      (by rw [secp256k1ReductionConstant_value]; decide +kernel) hv)
  exact fun s hs => point_lookup_valid_Y s hs.1 hs.2

theorem fig14LookupXState_ready (table : Nat → Nat) (hv : ∀ label, table label<ShorECDLP.p)
    (s : BasisState) (hs : PointLookupValid s) : PointLookupValid (fig14LookupXState table s) := by
  rw [fig14LookupXState_eq table hv s hs.1 hs.2]
  exact ⟨fig14ConstantXState_ready _ (hv _) s hs.1,
    ((fig14ConstantXState_correct (table (tableAddressValue pointLookupAddress s)) (hv _) s hs.1).2 836 (by decide +kernel)).trans hs.2⟩

theorem fig14LookupYState_ready (table : Nat → Nat) (hv : ∀ label, table label<ShorECDLP.p)
    (s : BasisState) (hs : PointLookupValid s) : PointLookupValid (fig14LookupYState table s) := by
  rw [fig14LookupYState_eq table hv s hs.1 hs.2]
  exact ⟨fig14ControlledConstantYState_ready _ (hv _) s hs.1,
    ((fig14ControlledConstantYState_correct (table (tableAddressValue pointLookupAddress s)) (hv _) s hs.1).2 836 (by decide +kernel)).trans hs.2⟩

private theorem point_lookup_address_frame (f : BasisState → BasisState) (s : BasisState)
    (hf : ∀ w, w∉List.range' 263 256 → w∉List.range' 580 256 → f s w=s w) :
    tableAddressValue pointLookupAddress (f s)=tableAddressValue pointLookupAddress s := by
  apply tableAddressValue_congr
  intro w hw
  apply hf w
  · simp [pointLookupAddress] at hw ⊢; omega
  · simp [pointLookupAddress] at hw ⊢; omega

theorem fig14LookupXState_address (table : Nat → Nat) (hv : ∀ label, table label<ShorECDLP.p)
    (s : BasisState) (hs : PointLookupValid s) :
    tableAddressValue pointLookupAddress (fig14LookupXState table s)=tableAddressValue pointLookupAddress s := by
  apply point_lookup_address_frame
  intro w hx _
  rw [fig14LookupXState_eq table hv s hs.1 hs.2]
  exact (fig14ConstantXState_correct (table (tableAddressValue pointLookupAddress s)) (hv _) s hs.1).2 w hx

theorem fig14LookupYState_address (table : Nat → Nat) (hv : ∀ label, table label<ShorECDLP.p)
    (s : BasisState) (hs : PointLookupValid s) :
    tableAddressValue pointLookupAddress (fig14LookupYState table s)=tableAddressValue pointLookupAddress s := by
  apply point_lookup_address_frame
  intro w _ hy
  rw [fig14LookupYState_eq table hv s hs.1 hs.2]
  exact (fig14ControlledConstantYState_correct (table (tableAddressValue pointLookupAddress s)) (hv _) s hs.1).2 w hy

/-- The fixed-layout addend bank is clean again after the X stage. -/
theorem fig14LookupXState_clean (table : Nat → Nat) (hv : ∀ label, table label<ShorECDLP.p)
    (s : BasisState) (hs : PointLookupValid s) :
    Clean (List.range' 7 256 ++ pointLookupPath) (fig14LookupXState table s) := by
  have h := (fig14LookupXState_ready table hv s hs).1.1
  intro w hw
  apply h w
  simp [pointLookupPath] at hw ⊢
  omega

theorem fig14LookupYState_clean (table : Nat → Nat) (hv : ∀ label, table label<ShorECDLP.p)
    (s : BasisState) (hs : PointLookupValid s) :
    Clean (List.range' 7 256 ++ pointLookupPath) (fig14LookupYState table s) := by
  have h := (fig14LookupYState_ready table hv s hs).1.1
  intro w hw
  apply h w
  simp [pointLookupPath] at hw ⊢
  omega

private theorem lookup_modular256_support (table : Nat → Nat) (bits paths input acc : List Wire)
    (q c r t f : Wire) (hi : input.length=256) (ha : acc.length=256) :
    (lookupModularAddProgram table bits paths input acc secp256k1ReductionConstantBits
      ShorECDLP.p q c r t f).wires ⊆ [q,c,r,t,f]++bits++paths++input++acc := by
  have hm (label : Nat) : tableWordMask input (table label) ⊆ input := tableBitsMask_subset _ _
  have hl := tableLookupProgram_support (fun label => tableWordMask input (table label)) bits paths input q hm
  have hb' : (controlledModularAdd input acc secp256k1ReductionConstantBits ShorECDLP.p q c r t f).wires ⊆
      [q,c,r,t,f]++input++acc := by
    have h := controlledModularAdd256_wires input acc (secp256k1ReductionConstantBits.tail) ShorECDLP.p
      q c r t f hi ha (by simp [secp256k1ReductionConstantBits])
      ShorECDLP.Secp256k1.p_prime.pos (by decide +kernel)
    exact h
  intro w hw
  simp only [lookupModularAddProgram,modularWires_seq] at hw
  rcases hw with (hw | hw) | hw
  · have h := hl hw
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    aesop
  · have h := hb' hw
    simp only [List.mem_append] at h ⊢
    aesop
  · have h := hl hw
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    aesop

theorem fig14LookupX_wires (table : Nat → Nat) : (fig14LookupX table).wires ⊆ List.range 855 := by
  have h := lookup_modular256_support table pointLookupAddress pointLookupPath
    (List.range' 7 256) (List.range' 263 256) 836 559 560 561 558 (by simp) (by simp)
  intro w hw
  have hh := h hw
  simp only [pointLookupAddress,pointLookupPath,List.mem_append,List.mem_cons,List.not_mem_nil,
    or_false,List.mem_range',List.mem_range] at hh ⊢
  rcases hh with (((((rfl | rfl | rfl | rfl | rfl) | ⟨i,hi,hwi⟩) | ⟨i,hi,hwi⟩) | ⟨i,hi,hwi⟩) | ⟨i,hi,hwi⟩) <;> omega

theorem fig14LookupY_wires (table : Nat → Nat) : (fig14LookupY table).wires ⊆ List.range 855 := by
  have h := lookup_modular256_support table pointLookupAddress pointLookupPath
    (List.range' 7 256) (List.range' 580 256) 836 559 560 561 558 (by simp) (by simp)
  intro w hw
  have hh := h hw
  simp only [pointLookupAddress,pointLookupPath,List.mem_append,List.mem_cons,List.not_mem_nil,
    or_false,List.mem_range',List.mem_range] at hh ⊢
  rcases hh with (((((rfl | rfl | rfl | rfl | rfl) | ⟨i,hi,hwi⟩) | ⟨i,hi,hwi⟩) | ⟨i,hi,hwi⟩) | ⟨i,hi,hwi⟩) <;> omega

end
end ShorECDLP.Paper2607_13816
