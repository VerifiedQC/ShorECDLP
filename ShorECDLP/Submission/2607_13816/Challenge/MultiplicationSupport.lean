import ShorECDLP.Submission.«2607_13816».Challenge.ControlSupport
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem modularSubProgram_support (n start : Nat) (input acc : List Wire) (modulus : List Bool)
    (p : Nat) (q c r t f : Wire) (support : List Wire)
    (hl : input.length = acc.length) (hk : modulus.length = acc.length) (hpos : 0 < acc.length)
    (hq : q ∈ support) (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support) (hf : f ∈ support)
    (hi : input ⊆ support) (ha : acc ⊆ support) :
    straightWires (modularSubProgram n start input acc modulus p q c r t f).2 ⊆ support := by
  have hsmall : q::c::f::input++acc ⊆ support := by
    simp only [List.append_subset,List.cons_subset]
    exact ⟨⟨hq,hc,hf,hi⟩,ha⟩
  have hsub : circuitWires (controlledSubCarry input acc q c f) ⊆ support :=
    (circuitWires_subset_of_usesOnly (controlledAddCarry_usesOnly input acc q c f).adjoint).trans hsmall
  have hcompare cursor := (uncontrolledCompareProgram_support n cursor acc input p c r t f).trans
    (show [c,r,t,f]++acc++input ⊆ support by
      simp only [List.append_subset,List.cons_subset,List.nil_subset,and_true]
      exact ⟨⟨⟨hc,hr,ht,hf⟩,ha⟩,hi⟩)
  have htake : acc.length = (input.take (acc.length-1)).length+1 := by
    simp only [List.length_take]; omega
  have hadd cursor := gidneyProgram_support n cursor acc (input.take (acc.length-1)) modulus f c r t
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
  simp only [modularSubProgram,prependCompiled_support,appendCompiled_support,literalProgram_support,List.append_subset]
  exact ⟨hlast,hadd _,hcompare _,hsub⟩

theorem modularDoubleProgram_support (n start : Nat) (acc dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (support : List Wire)
    (hd : acc.length = dirty.length) (hk : bits.length = acc.length)
    (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support) (hf : f ∈ support)
    (ha : acc ⊆ support) (hy : dirty ⊆ support) :
    straightWires (modularDoubleProgram n start acc dirty bits p c r t f).2 ⊆ support := by
  cases acc with
  | nil => exact List.nil_subset _
  | cons a acc =>
    have hcompare cursor := (uncontrolledCompareProgram_support n cursor (a::acc) dirty p c r t f).trans
      (show [c,r,t,f]++(a::acc)++dirty ⊆ support by
        simp only [List.append_subset,List.cons_subset,List.nil_subset,and_true]
        exact ⟨⟨⟨hc,hr,ht,hf⟩,(List.cons_subset.mp ha).1,(List.cons_subset.mp ha).2⟩,hy⟩)
    have htake : (a::acc).length = (dirty.take acc.length).length+1 := by
      simp only [List.length_take,List.length_cons] at hd ⊢; omega
    have hadd cursor := gidneyProgram_support n cursor (a::acc) (dirty.take acc.length) bits f c r t
      support htake hk hf hc hr ht ha (fun _ h => hy (List.mem_of_mem_take h))
    have hshift := (circuitWires_subset_of_usesOnly (doublingShift_usesOnly a f acc)).trans
      (List.cons_subset.mpr ⟨hf,ha⟩)
    have hlast : circuitWires [.CX a f] ⊆ support := by
      simp [circuitWires,gateWires,(List.cons_subset.mp ha).1,hf]
    simp only [modularDoubleProgram,prependCompiled_support,appendCompiled_support,literalProgram_support,List.append_subset]
    exact ⟨hshift,hcompare _,hadd _,hlast⟩

theorem modularHalveProgram_support (n start : Nat) (acc dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (support : List Wire)
    (hd : acc.length = dirty.length) (hk : bits.length = acc.length)
    (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support) (hf : f ∈ support)
    (ha : acc ⊆ support) (hy : dirty ⊆ support) :
    straightWires (modularHalveProgram n start acc dirty bits p c r t f).2 ⊆ support := by
  cases acc with
  | nil => exact List.nil_subset _
  | cons a acc =>
    have hcompare cursor := (uncontrolledCompareProgram_support n cursor (a::acc) dirty p c r t f).trans
      (show [c,r,t,f]++(a::acc)++dirty ⊆ support by
        simp only [List.append_subset,List.cons_subset,List.nil_subset,and_true]
        exact ⟨⟨⟨hc,hr,ht,hf⟩,(List.cons_subset.mp ha).1,(List.cons_subset.mp ha).2⟩,hy⟩)
    have htake : (a::acc).length = (dirty.take acc.length).length+1 := by
      simp only [List.length_take,List.length_cons] at hd ⊢; omega
    have hadd cursor := gidneyProgram_support n cursor (a::acc) (dirty.take acc.length) bits f c r t
      support htake hk hf hc hr ht ha (fun _ h => hy (List.mem_of_mem_take h))
    have hshift := (circuitWires_subset_of_usesOnly (doublingShift_usesOnly a f acc).adjoint).trans
      (List.cons_subset.mpr ⟨hf,ha⟩)
    have hfirst : circuitWires [.CX a f] ⊆ support := by
      simp [circuitWires,gateWires,(List.cons_subset.mp ha).1,hf]
    simp only [modularHalveProgram,prependCompiled_support,appendCompiled_support,literalProgram_support,List.append_subset]
    exact ⟨hfirst,hadd _,hcompare _,hshift⟩



theorem compiledIf_support {n start : Nat} (b : Prop) [Decidable b]
    (p q : (count : Nat) × Straight n start (start+count)) :
    straightWires (if b then p else q).2 = if b then straightWires p.2 else straightWires q.2 := by
  by_cases hb : b
  · rw [if_pos hb,if_pos hb]
  · rw [if_neg hb,if_neg hb]

attribute [local irreducible] modularAddProgram modularSubProgram modularDoubleProgram modularHalveProgram

theorem hornerProgram_support (n start : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (support : List Wire)
    (hd : input.length = acc.length) (hk : bits.length = acc.length) (hpos : 0 < acc.length)
    (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support) (hf : f ∈ support)
    (hqs : controls ⊆ support) (hi : input ⊆ support) (ha : acc ⊆ support) :
    straightWires (hornerProgram n start controls input acc bits p c r t f).2 ⊆ support := by
  induction controls generalizing start with
  | nil => exact List.nil_subset _
  | cons q qs ih =>
    have hb cursor := ih cursor (fun _ h => hqs (List.mem_cons_of_mem _ h))
    have hadd cursor := modularAddProgram_support n cursor input acc bits p q c r t f support hd hk hpos
      (hqs List.mem_cons_self) hc hr ht hf hi ha
    have hdbl cursor := modularDoubleProgram_support n cursor acc input bits p f r t c support hd.symm hk hf hr ht hc ha hi
    rw [hornerProgram]
    simp only [appendCompiled_support,compiledIf_support,List.append_subset]
    refine ⟨hb _,?_⟩
    split
    · exact hadd _
    · exact List.append_subset.mpr ⟨hdbl _,hadd _⟩

theorem hornerInverseProgram_support (n start : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (support : List Wire)
    (hd : input.length = acc.length) (hk : bits.length = acc.length) (hpos : 0 < acc.length)
    (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support) (hf : f ∈ support)
    (hqs : controls ⊆ support) (hi : input ⊆ support) (ha : acc ⊆ support) :
    straightWires (hornerInverseProgram n start controls input acc bits p c r t f).2 ⊆ support := by
  induction controls generalizing start with
  | nil => exact List.nil_subset _
  | cons q qs ih =>
    have hb cursor := ih cursor (fun _ h => hqs (List.mem_cons_of_mem _ h))
    have hsub cursor := modularSubProgram_support n cursor input acc bits p q c r t f support hd hk hpos
      (hqs List.mem_cons_self) hc hr ht hf hi ha
    have hhalf cursor := modularHalveProgram_support n cursor acc input bits p f r t c support hd.symm hk hf hr ht hc ha hi
    rw [hornerInverseProgram]
    simp only [appendCompiled_support,compiledIf_support,List.append_subset]
    refine ⟨hsub _,?_⟩
    split
    · exact List.nil_subset _
    · exact List.append_subset.mpr ⟨hhalf _,hb _⟩

theorem squareAddProgram_support (n start : Nat) (input acc : List Wire) (bits : List Bool)
    (p : Nat) (q copied c r t f : Wire) (support : List Wire)
    (hd : input.length = acc.length) (hk : bits.length = acc.length) (hpos : 0 < acc.length)
    (hq : q ∈ support) (hcopy : copied ∈ support) (hc : c ∈ support) (hr : r ∈ support)
    (ht : t ∈ support) (hf : f ∈ support) (hi : input ⊆ support) (ha : acc ⊆ support) :
    straightWires (squareAddProgram n start input acc bits p q copied c r t f).2 ⊆ support := by
  have hb := modularAddProgram_support n start input acc bits p copied c r t f support hd hk hpos hcopy hc hr ht hf hi ha
  have hx : circuitWires [.CX q copied] ⊆ support := by simp [circuitWires,gateWires,hq,hcopy]
  simp only [squareAddProgram,prependCompiled_support,appendCompiled_support,literalProgram_support,List.append_subset]
  exact ⟨hx,hb,hx⟩

theorem squareSubProgram_support (n start : Nat) (input acc : List Wire) (bits : List Bool)
    (p : Nat) (q copied c r t f : Wire) (support : List Wire)
    (hd : input.length = acc.length) (hk : bits.length = acc.length) (hpos : 0 < acc.length)
    (hq : q ∈ support) (hcopy : copied ∈ support) (hc : c ∈ support) (hr : r ∈ support)
    (ht : t ∈ support) (hf : f ∈ support) (hi : input ⊆ support) (ha : acc ⊆ support) :
    straightWires (squareSubProgram n start input acc bits p q copied c r t f).2 ⊆ support := by
  have hb := modularSubProgram_support n start input acc bits p copied c r t f support hd hk hpos hcopy hc hr ht hf hi ha
  have hx : circuitWires [.CX q copied] ⊆ support := by simp [circuitWires,gateWires,hq,hcopy]
  simp only [squareSubProgram,prependCompiled_support,appendCompiled_support,literalProgram_support,List.append_subset]
  exact ⟨hx,hb,hx⟩

attribute [local irreducible] squareAddProgram squareSubProgram

theorem squareProgram_support (n start : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (copied c r t f : Wire) (support : List Wire)
    (hd : input.length = acc.length) (hk : bits.length = acc.length) (hpos : 0 < acc.length)
    (hcopy : copied ∈ support) (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support) (hf : f ∈ support)
    (hqs : controls ⊆ support) (hi : input ⊆ support) (ha : acc ⊆ support) :
    straightWires (squareProgram n start controls input acc bits p copied c r t f).2 ⊆ support := by
  induction controls generalizing start with
  | nil => exact List.nil_subset _
  | cons q qs ih =>
    have hb cursor := ih cursor (fun _ h => hqs (List.mem_cons_of_mem _ h))
    have hadd cursor := squareAddProgram_support n cursor input acc bits p q copied c r t f support hd hk hpos
      (hqs List.mem_cons_self) hcopy hc hr ht hf hi ha
    have hdbl cursor := modularDoubleProgram_support n cursor acc input bits p f r t c support hd.symm hk hf hr ht hc ha hi
    rw [squareProgram]
    simp only [appendCompiled_support,compiledIf_support,List.append_subset]
    refine ⟨hb _,?_⟩
    split
    · exact hadd _
    · exact List.append_subset.mpr ⟨hdbl _,hadd _⟩

theorem squareInverseProgram_support (n start : Nat) (controls input acc : List Wire) (bits : List Bool)
    (p : Nat) (copied c r t f : Wire) (support : List Wire)
    (hd : input.length = acc.length) (hk : bits.length = acc.length) (hpos : 0 < acc.length)
    (hcopy : copied ∈ support) (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support) (hf : f ∈ support)
    (hqs : controls ⊆ support) (hi : input ⊆ support) (ha : acc ⊆ support) :
    straightWires (squareInverseProgram n start controls input acc bits p copied c r t f).2 ⊆ support := by
  induction controls generalizing start with
  | nil => exact List.nil_subset _
  | cons q qs ih =>
    have hb cursor := ih cursor (fun _ h => hqs (List.mem_cons_of_mem _ h))
    have hsub cursor := squareSubProgram_support n cursor input acc bits p q copied c r t f support hd hk hpos
      (hqs List.mem_cons_self) hcopy hc hr ht hf hi ha
    have hhalf cursor := modularHalveProgram_support n cursor acc input bits p f r t c support hd.symm hk hf hr ht hc ha hi
    rw [squareInverseProgram]
    simp only [appendCompiled_support,compiledIf_support,List.append_subset]
    refine ⟨hsub _,?_⟩
    split
    · exact List.nil_subset _
    · exact List.append_subset.mpr ⟨hhalf _,hb _⟩



attribute [local irreducible] squareProgram squareInverseProgram

theorem squareSubtractProgram_support (n start : Nat) (x y acc : List Wire) (correction modulus : List Bool)
    (p : Nat) (q copied c r t f : Wire) (support : List Wire)
    (hx : x.length = acc.length) (hy : y.length = acc.length)
    (hk : correction.length = acc.length) (hm : modulus.length = acc.length) (hpos : 0 < acc.length)
    (hq : q ∈ support) (hcopy : copied ∈ support) (hc : c ∈ support) (hr : r ∈ support)
    (ht : t ∈ support) (hf : f ∈ support)
    (hsx : x ⊆ support) (hsy : y ⊆ support) (hsa : acc ⊆ support) :
    straightWires (squareSubtractProgram n start x y acc correction modulus p q copied c r t f).2 ⊆ support := by
  have hs cursor := squareProgram_support n cursor y y acc correction p copied c r t f support hy hk hpos hcopy hc hr ht hf hsy hsy hsa
  have hu cursor := squareInverseProgram_support n cursor y y acc modulus p copied c r t f support hy hm hpos hcopy hc hr ht hf hsy hsy hsa
  have hsub cursor := modularSubProgram_support n cursor acc x modulus p q copied f r c support hx.symm
    (hm.trans hx.symm) (hx.symm ▸ hpos) hq hcopy hf hr hc hsa hsx
  simp only [squareSubtractProgram,appendCompiled_support,List.append_subset]
  exact ⟨hs _,hsub _,hu _⟩

theorem pointSquareProgram_support_static (n start : Nat) :
    straightWires (pointSquareProgram n start).2 ⊆ windowBaseSupport := by
  apply squareSubtractProgram_support
  all_goals try simp [secp256k1ReductionConstantBits,windowBaseSupport]
  all_goals intro w hw
  all_goals simp only [List.mem_range'_1,List.mem_cons,List.mem_append,List.mem_range] at hw ⊢
  all_goals omega


theorem multiplyWorkProgram_support_static (n start : Nat) :
    straightWires (multiplyWorkProgram n start).2 ⊆ windowBaseSupport := by
  apply hornerProgram_support
  all_goals try simp [secp256k1ReductionConstantBits,windowBaseSupport]
  all_goals intro w hw
  all_goals simp only [List.mem_range'_1,List.mem_cons,List.mem_append,List.mem_range] at hw ⊢
  all_goals omega

theorem multiplyDataProgram_support_static (n start : Nat) :
    straightWires (multiplyDataProgram n start).2 ⊆ windowBaseSupport := by
  apply hornerProgram_support
  all_goals try simp [secp256k1ReductionConstantBits,windowBaseSupport]
  all_goals intro w hw
  all_goals simp only [List.mem_range'_1,List.mem_cons,List.mem_append,List.mem_range] at hw ⊢
  all_goals omega

theorem unmultiplyDataProgram_support_static (n start : Nat) :
    straightWires (unmultiplyDataProgram n start).2 ⊆ windowBaseSupport := by
  apply hornerInverseProgram_support
  all_goals try simp [windowBaseSupport]
  all_goals intro w hw
  all_goals simp only [List.mem_range'_1,List.mem_cons,List.mem_append,List.mem_range] at hw ⊢
  all_goals omega

theorem xNegateProgram_support_static (n start : Nat) :
    straightWires (xNegateProgram n start).2 ⊆ windowBaseSupport := by
  apply modularNegateProgram_support
  all_goals try simp [windowBaseSupport]
  all_goals intro w hw
  all_goals simp only [List.mem_range'_1,List.mem_cons,List.mem_append,List.mem_range] at hw ⊢
  all_goals omega

end ShorECDLP.Paper2607_13816.ChallengeMigration
