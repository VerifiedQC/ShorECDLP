import ShorECDLP.Submission.«2607_13816».Arithmetic.UncontrolledModular
import ShorECDLP.Submission.«2607_13816».Arithmetic.ModularNegate
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
private theorem constant_support (A D : List Wire) (K : List Bool) (q c r t : Wire)
    (hA : A.length=256) (hD : D.length=255) (hK : K.length=256) :
    (controlledGidneyAddConst A D K q c r t).wires ⊆ [q,c,r,t]++A++D := by
  cases A with
  | nil => simp at hA
  | cons a as =>
    cases D with
    | nil => simp at hD
    | cons d ds =>
      cases K with
      | nil => simp at hK
      | cons k ks => exact controlledGidneyAddConst_wires_subset a d q c r t as ds k ks
private theorem comparison_support (A D : List Wire) (k : Nat) (c r t f : Wire)
    (hA : A.length=256) (hD : D.length=256) (hk : 0<k) (hkb : k<2^256) :
    (gidneyCompareGE A D k c r t f).wires ⊆ [c,r,t,f]++A++D := by
  cases A with
  | nil => simp at hA
  | cons a as =>
    have hh := gidneyCompareGE_metrics a as D k c r t f (hA.trans hD.symm) hk (by simpa only [hA] using hkb)
    intro w hw
    exact (hh.2.2.2.2 w).mp hw
private theorem controlledLT_support (A D : List Wire) (k : Nat) (q c r t f : Wire)
    (hA : A.length=256) (hD : D.length=256) (hk : k<2^256) :
    (controlledGidneyCompareLT A D k q c r t f).wires ⊆ [q,c,r,t,f]++A++D := by
  by_cases hz : k=0
  · simp [controlledGidneyCompareLT,hz,AdaptiveCircuit.wires]
  · cases A with
    | nil => simp at hA
    | cons a as =>
      have hh := controlledGidneyCompareLT_metrics a as D k q c r t f (hA.trans hD.symm)
        (by omega) (by simpa only [hA] using hk)
      intro w hw
      exact (hh.2.2.2 w).mp hw
private theorem uncontrolledLT_support (A D : List Wire) (k : Nat) (c r t f : Wire)
    (hA : A.length=256) (hD : D.length=256) (hk : k<2^256) :
    (gidneyCompareLT A D k c r t f).wires ⊆ [c,r,t,f]++A++D := by
  by_cases hz : k=0
  · simp [gidneyCompareLT,hz,AdaptiveCircuit.wires]
  · have hh := comparison_support A D k c r t f hA hD (by omega) hk
    have hl : ¬2^A.length≤k := by rw [hA]; omega
    intro w hw
    simp only [gidneyCompareLT,if_neg hz,if_neg hl,AdaptiveCircuit.wires,circuitWires,
      List.flatMap_cons,List.flatMap_nil,List.append_nil,gateWires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | hw
    · simp
    · exact hh hw
private theorem borrow_support (A D : List Wire) (K : List Bool) (q c r t : Wire)
    (hA : A.length=256) (hD : D.length=256) (hK : K.length=256) :
    (controlledGidneyAddConst A (D.take (A.length-1)) K q c r t).wires ⊆ [q,c,r,t]++A++D := by
  have hh := constant_support A (D.take (A.length-1)) K q c r t hA (by simp [hA,hD]) hK
  intro w hw
  have hm := hh hw
  simp only [List.mem_append] at hm ⊢
  rcases hm with hm | hm
  · exact Or.inl hm
  · exact Or.inr (List.mem_of_mem_take hm)

theorem controlledConstantModularAdd256_wires_subset (A D : List Wire) (K R : List Bool)
    (p : Nat) (q c r t f : Wire) (hA : A.length=256) (hD : D.length=256)
    (hK : K.length=256) (hR : R.length=256) (hk : boolWordToNat K<2^256)
    (hp0 : 0<p) (hp : p<2^256) :
    (controlledConstantModularAdd A D K R p q c r t f).wires ⊆ [q,c,r,t,f]++A++D := by
  have h1 := borrow_support A D K q c r t hA hD hK
  have h2 := controlledLT_support A D (boolWordToNat K) q c r t f hA hD hk
  have h3 := comparison_support A D p c r t f hA hD hp0 hp
  have h4 := borrow_support A D R f c r t hA hD hR
  simp only [List.subset_def,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h1 h2 h3 h4
  intro w hw
  simp only [controlledConstantModularAdd,modularWires_seq] at hw
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  rcases hw with hw | hw | hw | hw | hw
  · have h := h1 hw; tauto
  · exact h2 hw
  · have h := h3 hw; tauto
  · have h := h4 hw; tauto
  · exact h2 hw

theorem uncontrolledConstantModularAdd256_wires_subset (A D : List Wire) (K R : List Bool)
    (p : Nat) (c r t f : Wire) (hA : A.length=256) (hD : D.length=256)
    (hK : K.length=256) (hR : R.length=256) (hk : boolWordToNat K<2^256)
    (hp0 : 0<p) (hp : p<2^256) :
    (uncontrolledConstantModularAdd A D K R p c r t f).wires ⊆ [c,r,t,f]++A++D := by
  have hfirst := gidneyAddConst256_wires_subset A (D.take (A.length-1)) K c r t hA (by simp [hA,hD]) hK
  have h1 : (gidneyAddConst A (D.take (A.length-1)) K c r t).wires ⊆ [c,r,t]++A++D := by
    intro w hw
    have hm := hfirst hw
    simp only [List.mem_append] at hm ⊢
    rcases hm with hm | hm
    · exact Or.inl hm
    · exact Or.inr (List.mem_of_mem_take hm)
  have h2 := uncontrolledLT_support A D (boolWordToNat K) c r t f hA hD hk
  have h3 := comparison_support A D p c r t f hA hD hp0 hp
  have h4 := borrow_support A D R f c r t hA hD hR
  simp only [List.subset_def,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h1 h2 h3 h4
  intro w hw
  simp only [uncontrolledConstantModularAdd,modularWires_seq] at hw
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  rcases hw with hw | hw | hw | hw | hw
  · have h := h1 hw; tauto
  · exact h2 hw
  · exact h3 hw
  · have h := h4 hw; tauto
  · exact h2 hw

private theorem controlledGE1_support (A D : List Wire) (q c r t f : Wire)
    (hA : A.length=256) (hD : D.length=256) :
    (controlledGidneyCompareGE A D 1 q c r t f).wires ⊆ [q,c,r,t,f]++A++D := by
  have hh := controlledLT_support A D 1 q c r t f hA hD (by decide)
  have hl : ¬2^A.length≤1 := by rw [hA]; decide
  intro w hw
  apply hh
  simp only [controlledGidneyCompareLT,show ¬(1:Nat)=0 from by decide,if_false,if_neg hl,
    AdaptiveCircuit.wires,List.mem_append]
  exact Or.inr hw
private theorem complement_support (A : List Wire) (q : Wire) :
    circuitWires (controlledComplement A q) ⊆ q::A := by
  intro w hw
  simp only [circuitWires,controlledComplement,List.mem_flatMap,List.mem_map] at hw
  obtain ⟨g,⟨a,ha,rfl⟩,hw⟩ := hw
  simp only [gateWires,List.mem_cons,List.not_mem_nil,or_false] at hw ⊢
  rcases hw with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr ha

theorem controlledModularNegate256_wires_subset (A D : List Wire) (K : List Bool) (q c r t f : Wire)
    (hA : A.length=256) (hD : D.length=256) (hK : K.length=256) :
    (controlledModularNegate A D K q c r t f).wires ⊆ [q,c,r,t,f]++A++D := by
  have h1 := controlledGE1_support A D q c r t f hA hD
  have h2 := complement_support A q
  have h3 := borrow_support A D ((List.range A.length).map (Nat.testBit 1)) q c r t hA hD (by simp [hA])
  have h4 := borrow_support A D K f c r t hA hD hK
  simp only [List.subset_def,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h1 h2 h3 h4
  intro w hw
  simp only [controlledModularNegate,modularWires_seq,AdaptiveCircuit.wires,List.mem_append] at hw
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  rcases hw with hw | hw | hw | hw | hw
  · exact h1 hw
  · have h := h2 hw; tauto
  · have h := h3 hw; tauto
  · have h := h4 hw; tauto
  · exact h1 hw


end ShorECDLP.Paper2607_13816
