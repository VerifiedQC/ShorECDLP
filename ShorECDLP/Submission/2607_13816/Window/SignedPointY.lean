import ShorECDLP.Submission.«2607_13816».Window.SignedLookup
import ShorECDLP.Submission.«2607_13816».Window.PointStages
import ShorECDLP.Submission.«2607_13816».Arithmetic.ConstantSupport
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section

def signedPointLookupY (table : Nat → Nat) : AdaptiveCircuit :=
  signedLookupModularAddProgram table pointLookupAddress pointLookupPath
    (List.range' 7 256) (List.range' 580 256) secp256k1ReductionConstantBits
    ShorECDLP.p 836 854 559 560 561 558

def signedPointLookupYState (table : Nat → Nat) : BasisState → BasisState :=
  signedLookupModularAddState table pointLookupAddress (List.range' 7 256) (List.range' 580 256)
    secp256k1ReductionConstantBits ShorECDLP.p 836 854 559 558

private theorem signed_point_valid (s : BasisState) (hs : PointLookupValid s) :
    LookupModularValid pointLookupPath (List.range' 7 256) (List.range' 580 256)
      ShorECDLP.p 836 559 560 561 558 s := by
  refine ⟨?_,?_,hs.2,?_,?_,?_,?_,hs.1.2.2.2⟩
  · intro w hw
    apply hs.1.1 w
    simp [pointLookupPath] at hw ⊢
    omega
  · intro w hw
    apply hs.1.1 w
    simp at hw ⊢
    omega
  · exact hs.1.1 559 (by decide +kernel)
  · exact hs.1.1 560 (by decide +kernel)
  · exact hs.1.1 561 (by decide +kernel)
  · exact hs.1.1 558 (by decide +kernel)

private theorem signed_point_input_disjoint :
    (836::pointLookupAddress++pointLookupPath).Disjoint (List.range' 7 256) := by
  apply List.disjoint_left.mpr
  intro w hw ht
  simp only [pointLookupAddress,pointLookupPath,List.mem_cons,List.mem_append,List.mem_range'] at hw ht
  rcases hw with (rfl | ⟨i,hi,hwi⟩) | ⟨i,hi,hwi⟩ <;> obtain ⟨j,hj,hwj⟩ := ht <;> omega

private theorem signed_point_path_disjoint : pointLookupPath.Disjoint (List.range' 580 256) := by
  apply List.disjoint_left.mpr
  intro w hw ht
  simp only [pointLookupPath,List.mem_range'] at hw ht
  omega

private theorem signed_point_address_disjoint : pointLookupAddress.Disjoint (List.range' 580 256) := by
  apply List.disjoint_left.mpr
  intro w hw ht
  simp only [pointLookupAddress,List.mem_range'] at hw ht
  omega

private theorem signed_point_add_layout : ([836,559,560,561,558] ++ List.range' 7 256 ++ List.range' 580 256 : List Wire).Nodup := by decide +kernel
private theorem signed_point_neg_layout : ([854,559,560,561,558] ++ List.range' 580 256 ++ List.range' 7 256 : List Wire).Nodup := by decide +kernel

theorem signedPointLookupYState_correct (table : Nat → Nat) (hv : ∀ a, table a<ShorECDLP.p)
    (s : BasisState) (hs : PointLookupValid s) :
    boolWordToNat (wireValues (List.range' 580 256) (signedPointLookupYState table s))=
      (if s 854 then (boolWordToNat (wireValues (List.range' 580 256) s)+table (tableAddressValue pointLookupAddress s))%ShorECDLP.p
       else (boolWordToNat (wireValues (List.range' 580 256) s)+ShorECDLP.p-table (tableAddressValue pointLookupAddress s))%ShorECDLP.p) ∧
    ∀ w, w∉List.range' 580 256 → signedPointLookupYState table s w=s w := by
  exact signedLookupModularAddState_correct table pointLookupAddress pointLookupPath
    (List.range' 7 256) (List.range' 580 256) secp256k1ReductionConstantBits ShorECDLP.p 836 854 559 560 561 558
    signed_point_input_disjoint signed_point_path_disjoint signed_point_address_disjoint
    (by simp) (by simp) (by simp [secp256k1ReductionConstantBits]) signed_point_add_layout signed_point_neg_layout
    ShorECDLP.Secp256k1.p_prime.pos (by decide +kernel)
    (by rw [secp256k1ReductionConstant_value]; decide +kernel) hv s (signed_point_valid s hs)

def signedPointTableValue (table : Nat → Nat) (s : BasisState) : Nat :=
  if s 854 then table (tableAddressValue pointLookupAddress s)
  else (ShorECDLP.p-table (tableAddressValue pointLookupAddress s))%ShorECDLP.p

theorem signedPointTableValue_lt (table : Nat → Nat) (hv : ∀ a, table a<ShorECDLP.p) (s : BasisState) :
    signedPointTableValue table s<ShorECDLP.p := by
  unfold signedPointTableValue
  split
  · exact hv _
  · exact Nat.mod_lt _ ShorECDLP.Secp256k1.p_prime.pos

theorem signedPointLookupYState_eq (table : Nat → Nat) (hv : ∀ a, table a<ShorECDLP.p)
    (s : BasisState) (hs : PointLookupValid s) :
    signedPointLookupYState table s=fig14ControlledConstantYState (signedPointTableValue table s) s := by
  have h := signedPointLookupYState_correct table hv s hs
  have hc := fig14ControlledConstantYState_correct (signedPointTableValue table s) (signedPointTableValue_lt table hv s) s hs.1
  have he : boolWordToNat (wireValues (List.range' 580 256) (signedPointLookupYState table s))=
      boolWordToNat (wireValues (List.range' 580 256) (fig14ControlledConstantYState (signedPointTableValue table s) s)) := by
    rw [h.1,hc.1]
    simp only [hs.2, signedPointTableValue]
    simp only [ite_true]
    cases hsg : s 854
    · simp only [Bool.false_eq_true,if_false]
      have he : boolWordToNat (wireValues (List.range' 580 256) s)+(ShorECDLP.p-table (tableAddressValue pointLookupAddress s))=
          boolWordToNat (wireValues (List.range' 580 256) s)+ShorECDLP.p-table (tableAddressValue pointLookupAddress s) := by
        have ht := hv (tableAddressValue pointLookupAddress s)
        omega
      rw [←he]
      simp only [Nat.add_mod,Nat.mod_mod]
    · simp
  have he' := boolWordToNat_injective_of_length (by simp [wireValues]) he
  funext w
  by_cases hw : w∈List.range' 580 256
  · exact List.map_inj_left.mp he' w hw
  · exact (h.2 w hw).trans (hc.2 w hw).symm

theorem signedPointLookupY_coherent (table : Nat → Nat) (hv : ∀ a, table a<ShorECDLP.p) :
    CoherentlyImplementsOn (signedPointLookupY table)
      (Finsupp.lmapDomain ℂ ℂ (signedPointLookupYState table)) PointLookupValid := by
  have h := signedLookupModularAddProgram_coherent table pointLookupAddress pointLookupPath
    (List.range' 7 256) (List.range' 580 256) secp256k1ReductionConstantBits ShorECDLP.p 836 854 559 560 561 558
    (by decide +kernel) (by decide +kernel)
    signed_point_input_disjoint signed_point_path_disjoint signed_point_address_disjoint
    (by simp) (by simp) (by simp [secp256k1ReductionConstantBits]) signed_point_add_layout signed_point_neg_layout
    ShorECDLP.Secp256k1.p_prime.pos (by decide +kernel)
    (by rw [secp256k1ReductionConstant_value]; decide +kernel) hv
  obtain ⟨cs,ha,hm⟩ := h
  exact ⟨cs,ha.imp (fun b c hb s hs => hb s (signed_point_valid s hs)),hm⟩

theorem signedPointLookupYState_ready (table : Nat → Nat) (hv : ∀ a, table a<ShorECDLP.p)
    (s : BasisState) (hs : PointLookupValid s) : PointLookupValid (signedPointLookupYState table s) := by
  rw [signedPointLookupYState_eq table hv s hs]
  exact ⟨fig14ControlledConstantYState_ready _ (signedPointTableValue_lt table hv s) s hs.1,
    ((fig14ControlledConstantYState_correct (signedPointTableValue table s) (signedPointTableValue_lt table hv s) s hs.1).2 836 (by decide +kernel)).trans hs.2⟩

theorem signedPointLookupYState_address (table : Nat → Nat) (hv : ∀ a, table a<ShorECDLP.p)
    (s : BasisState) (hs : PointLookupValid s) :
    tableAddressValue pointLookupAddress (signedPointLookupYState table s)=tableAddressValue pointLookupAddress s := by
  apply tableAddressValue_congr
  intro w hw
  apply (signedPointLookupYState_correct table hv s hs).2 w
  exact fun hy => signed_point_address_disjoint hw hy

theorem signedPointLookupYState_sign (table : Nat → Nat) (hv : ∀ a, table a<ShorECDLP.p)
    (s : BasisState) (hs : PointLookupValid s) : signedPointLookupYState table s 854=s 854 :=
  (signedPointLookupYState_correct table hv s hs).2 854 (by decide +kernel)


private theorem signed_point_neg_support :
    (negativeControlledModularNegate (List.range' 580 256) (List.range' 7 256)
      (constantBits 256 ShorECDLP.p) 854 559 560 561 558).wires ⊆ List.range 855 := by
  intro w hw
  have h := negativeControlledModularNegate_wires _ _ _ 854 559 560 561 558 hw
  simp only [List.mem_cons] at h
  rcases h with rfl | h
  · decide +kernel
  · have hh := controlledModularNegate256_wires_subset (List.range' 580 256) (List.range' 7 256)
      (constantBits 256 ShorECDLP.p) 854 559 560 561 558 (by simp) (by simp) (constantBits_length _ _) h
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_range',List.mem_range] at hh ⊢
    rcases hh with ((rfl | rfl | rfl | rfl | rfl) | ⟨i,hi,hwi⟩) | ⟨i,hi,hwi⟩ <;> omega

theorem signedPointLookupY_wires (table : Nat → Nat) : (signedPointLookupY table).wires ⊆ List.range 855 := by
  intro w hw
  simp only [signedPointLookupY,signedLookupModularAddProgram,modularWires_seq,List.length_range'] at hw
  rcases hw with (hw | hw) | hw
  · exact signed_point_neg_support hw
  · exact fig14LookupY_wires table hw
  · exact signed_point_neg_support hw


/-- The sign is separate from all fifteen address wires. -/
theorem signedPointLookup_address_layout : pointLookupAddress.length=15 ∧
    pointLookupPath.length=15 ∧ 854∉pointLookupAddress ∧ 854∉pointLookupPath := by
  decide +kernel

theorem signedPointLookupY_resources (table : Nat → Nat) :
    (signedPointLookupY table).tCount =
      2*(negativeControlledModularNegate (List.range' 580 256) (List.range' 7 256)
        (constantBits 256 ShorECDLP.p) 854 559 560 561 558).tCount+
      (controlledModularAdd (List.range' 7 256) (List.range' 580 256) secp256k1ReductionConstantBits
        ShorECDLP.p 836 559 560 561 558).tCount+458738 ∧
    (signedPointLookupY table).measurementCount =
      2*(negativeControlledModularNegate (List.range' 580 256) (List.range' 7 256)
        (constantBits 256 ShorECDLP.p) 854 559 560 561 558).measurementCount+
      (controlledModularAdd (List.range' 7 256) (List.range' 580 256) secp256k1ReductionConstantBits
        ShorECDLP.p 836 559 560 561 558).measurementCount+65534 := by
  have h := signedLookupModularAddProgram_resources table pointLookupAddress pointLookupPath
    (List.range' 7 256) (List.range' 580 256) secp256k1ReductionConstantBits ShorECDLP.p
    836 854 559 560 561 558 (by decide +kernel) (by decide +kernel)
  simp only [List.length_range', show pointLookupAddress.length=15 from rfl] at h
  rw [show 14*(2^15-1)=458738 by decide +kernel, show 2*(2^15-1)=65534 by decide +kernel] at h
  exact h

end
end ShorECDLP.Paper2607_13816
