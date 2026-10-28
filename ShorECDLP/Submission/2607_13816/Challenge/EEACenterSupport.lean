import ShorECDLP.Submission.«2607_13816».Challenge.ControlSupport
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem constMinusProgram_support (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (q c r t : Wire) (support : List Wire)
    (hd : input.length = dirty.length+1) (hk : bits.length = input.length)
    (hq : q ∈ support) (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support)
    (hi : input ⊆ support) (hy : dirty ⊆ support) :
    straightWires (constMinusProgram n start input dirty bits q c r t).2 ⊆ support := by
  have hx : circuitWires (controlledComplement input q) ⊆ support := by
    intro w hw
    simp only [controlledComplement,circuitWires,List.mem_flatMap,List.mem_map] at hw
    obtain ⟨g,⟨z,hz,rfl⟩,hw⟩ := hw
    simp only [gateWires,List.mem_cons,List.mem_nil_iff,or_false] at hw
    rcases hw with rfl | rfl
    · exact hq
    · exact hi hz
  have hinc := gidneyProgram_support n start input dirty ((List.range input.length).map (Nat.testBit 1)) q c r t support hd (by simp) hq hc hr ht hi hy
  have hbody cursor := gidneyProgram_support n cursor input dirty bits q c r t support hd hk hq hc hr ht hi hy
  simp only [constMinusProgram,prependCompiled_support,appendCompiled_support,List.append_subset]
  exact ⟨hx,hinc,hbody _⟩

theorem eeaCenterProgram_support (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t iter : Wire) (support : List Wire)
    (hd : input.length = dirty.length) (hk : bits.length = input.length) (hpos : 0 < input.length)
    (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support) (he : iter ∈ support)
    (hi : input ⊆ support) (hy : dirty ⊆ support) :
    straightWires (eeaCenterProgram n start input dirty bits p c r t iter).2 ⊆ support := by
  have htake : input.length = (dirty.take (input.length-1)).length+1 := by
    simp only [List.length_take]; omega
  have hb cursor := constMinusProgram_support n cursor input (dirty.take (input.length-1)) bits iter c r t support htake hk he hc hr ht hi (fun _ h => hy (List.mem_of_mem_take h))
  have htst := (uncontrolledCompareProgram_support n start input dirty (p/2+1) c r t iter).trans
    (show [c,r,t,iter]++input++dirty ⊆ support by
      simp only [List.append_subset,List.cons_subset,List.nil_subset,and_true]
      exact ⟨⟨⟨hc,hr,ht,he⟩,hi⟩,hy⟩)
  simp only [eeaCenterProgram,appendCompiled_support,List.append_subset]
  exact ⟨htst,hb _⟩

theorem eeaUncenterProgram_support (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t iter : Wire) (support : List Wire)
    (hd : input.length = dirty.length) (hk : bits.length = input.length) (hpos : 0 < input.length)
    (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support) (he : iter ∈ support)
    (hi : input ⊆ support) (hy : dirty ⊆ support) :
    straightWires (eeaUncenterProgram n start input dirty bits p c r t iter).2 ⊆ support := by
  have htake : input.length = (dirty.take (input.length-1)).length+1 := by
    simp only [List.length_take]; omega
  have hb := constMinusProgram_support n start input (dirty.take (input.length-1)) bits iter c r t support htake hk he hc hr ht hi (fun _ h => hy (List.mem_of_mem_take h))
  have htst cursor := (uncontrolledCompareProgram_support n cursor input dirty (p/2+1) c r t iter).trans
    (show [c,r,t,iter]++input++dirty ⊆ support by
      simp only [List.append_subset,List.cons_subset,List.nil_subset,and_true]
      exact ⟨⟨⟨hc,hr,ht,he⟩,hi⟩,hy⟩)
  simp only [eeaUncenterProgram,appendCompiled_support,List.append_subset]
  exact ⟨hb,htst _⟩

theorem eeaParityProgram_support (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (c r t iter : Wire) (support : List Wire)
    (hd : input.length = dirty.length+1) (hk : bits.length = input.length)
    (hc : c ∈ support) (hr : r ∈ support) (ht : t ∈ support) (he : iter ∈ support)
    (hi : input ⊆ support) (hy : dirty ⊆ support) :
    straightWires (eeaParityProgram n start input dirty bits c r t iter).2 ⊆ support := by
  have hb := constMinusProgram_support n start input dirty bits iter c r t support hd hk he hc hr ht hi hy
  have hx : circuitWires [.X iter] ⊆ support := by simp [circuitWires,gateWires,he]
  simp only [eeaParityProgram,prependCompiled_support,appendCompiled_support,literalProgram_support,List.append_subset]
  exact ⟨hx,hb,hx⟩
end ShorECDLP.Paper2607_13816.ChallengeMigration
