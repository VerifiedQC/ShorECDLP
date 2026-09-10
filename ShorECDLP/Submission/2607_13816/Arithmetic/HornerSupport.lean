import ShorECDLP.Submission.«2607_13816».Arithmetic.HornerInverse
import ShorECDLP.Submission.«2607_13816».Arithmetic.SquareSubtract

/-!
# Physical support of width-256 Horner arithmetic

Both source directions use only their control, input and accumulator banks plus
the four named helpers. The bound includes measurement corrections and borrowed
work in the input bank; it requires no particular register labels.
-/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
private theorem constant256_support (acc dirty : List Wire) (bits : List Bool) (q c r t : Wire)
    (ha : acc.length=256) (hd : dirty.length=255) (hb : bits.length=255) :
    (controlledGidneyAddConst acc dirty (true::bits) q c r t).wires ⊆ [q,c,r,t]++acc++dirty := by
  cases acc with
  | nil => simp at ha
  | cons a rest =>
    cases dirty with
    | nil => simp at hd
    | cons d ds =>
      have h := controlledGidneyAddConst_wires a d q c r t rest ds bits
        (by simp only [List.length_cons] at ha; omega)
        (by simp only [List.length_cons] at ha hd; omega)
      intro w hw
      exact (h w).mp hw
private theorem comparison256_support (acc dirty : List Wire) (p : Nat) (c r t f : Wire)
    (ha : acc.length=256) (hd : dirty.length=256) (hp0 : 0<p) (hp : p<2^256) :
    (gidneyCompareGE acc dirty p c r t f).wires ⊆ [c,r,t,f]++acc++dirty := by
  cases acc with
  | nil => simp at ha
  | cons a rest =>
    have h := gidneyCompareGE_metrics a rest dirty p c r t f (by omega) hp0 (by simpa only [ha] using hp)
    intro w hw
    exact (h.2.2.2.2 w).mp hw
private theorem compareLT256_support (acc input : List Wire) (q c f : Wire)
    (ha : acc.length=256) (hi : input.length=256) :
    circuitWires (controlledCompareLT acc input q c f) ⊆ [q,c,f]++acc++input := by
  cases acc with
  | nil => simp at ha
  | cons a rest =>
    intro w hw
    exact (controlledCompareLT_wires a rest input q c f w (by omega)).mp hw
private theorem unitary_support (g : Circuit) (support : List Wire) (h : PaperCircuitUsesOnly support g) :
    circuitWires g ⊆ support := by
  intro w hw
  obtain ⟨gate,hgate,hw⟩ := List.mem_flatMap.mp hw
  exact h gate hgate w hw
private theorem modularAdd256_support (input acc : List Wire) (bits : List Bool) (p : Nat)
    (q c r t f : Wire) (hi : input.length=256) (ha : acc.length=256) (hb : bits.length=255)
    (hp0 : 0<p) (hp : p<2^256) :
    (controlledModularAdd input acc (true::bits) p q c r t f).wires ⊆ [q,c,r,t,f]++input++acc := by
  have hfirst := unitary_support _ _ (controlledAddCarry_usesOnly input acc q c f)
  have hcompare := comparison256_support acc input p c r t f ha hi hp0 hp
  have hconstant := constant256_support acc (input.take (acc.length-1)) bits f c r t ha
    (by rw [List.length_take,ha,hi]; decide) hb
  have hlast := compareLT256_support acc input q c f ha hi
  intro w hw
  simp only [controlledModularAdd,AdaptiveCircuit.wires,modularWires_seq,List.mem_append,
    List.not_mem_nil,or_false] at hw
  rcases hw with hw | hw | hw | hw
  · have h := hfirst hw
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    aesop
  · have h := hcompare hw
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    aesop
  · have h := hconstant hw
    simp only [List.mem_append] at h
    rcases h with (h | h) | h
    · simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
      aesop
    · simp only [List.mem_append]; aesop
    · have hm := List.mem_of_mem_take h
      simp only [List.mem_append]; aesop
  · have h := hlast hw
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    aesop
private theorem modularSub256_support (input acc : List Wire) (bits : List Bool) (p : Nat)
    (q c r t f : Wire) (hi : input.length=256) (ha : acc.length=256) (hb : bits.length=255)
    (hp0 : 0<p) (hp : p<2^256) :
    (controlledModularSub input acc (true::bits) p q c r t f).wires ⊆ [q,c,r,t,f]++input++acc := by
  have hfirst := unitary_support _ _ (controlledAddCarry_usesOnly input acc q c f).adjoint
  have hcompare := comparison256_support acc input p c r t f ha hi hp0 hp
  have hconstant := constant256_support acc (input.take (acc.length-1)) bits f c r t ha
    (by rw [List.length_take,ha,hi]; decide) hb
  have hlast := compareLT256_support acc input q c f ha hi
  intro w hw
  simp only [controlledModularSub,AdaptiveCircuit.wires,modularWires_seq,List.mem_append,
    List.not_mem_nil,or_false] at hw
  rcases hw with hw | hw | hw | hw
  · have h := hlast hw
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    aesop
  · have h := hconstant hw
    simp only [List.mem_append] at h
    rcases h with (h | h) | h
    · simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
      aesop
    · simp only [List.mem_append]; aesop
    · have hm := List.mem_of_mem_take h
      simp only [List.mem_append]; aesop
  · have h := hcompare hw
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    aesop
  · have h := hfirst hw
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    aesop

private theorem double256_support (acc dirty : List Wire) (bits : List Bool) (p : Nat)
    (c r t f : Wire) (ha : acc.length=256) (hd : dirty.length=256) (hb : bits.length=255)
    (hp0 : 0<p) (hp : p<2^256) :
    (modularDouble acc dirty (true::bits) p c r t f).wires ⊆ [c,r,t,f]++acc++dirty := by
  cases acc with
  | nil => simp at ha
  | cons a rest =>
    have hs := unitary_support _ _ (doublingShift_usesOnly a f rest)
    have hc := comparison256_support (a::rest) dirty p c r t f ha hd hp0 hp
    have hk := constant256_support (a::rest) (dirty.take rest.length) bits f c r t ha
      (by simp only [List.length_take]; simp only [List.length_cons] at ha; omega) hb
    intro w hw
    simp only [modularDouble,AdaptiveCircuit.wires,modularWires_seq,List.mem_append,
      List.not_mem_nil,or_false] at hw
    rcases hw with hw | hw | hw | hw
    · have h := hs hw
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
      aesop
    · exact hc hw
    · have h := hk hw
      simp only [List.mem_append] at h
      rcases h with (h | h) | h
      · simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
        aesop
      · simp only [List.mem_append]; aesop
      · have hm := List.mem_of_mem_take h
        simp only [List.mem_append]; aesop
    · simp only [circuitWires,List.flatMap_cons,List.flatMap_nil,List.append_nil,gateWires,
        List.mem_cons,List.not_mem_nil,or_false] at hw
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
      aesop

private theorem halve256_support (acc dirty : List Wire) (bits : List Bool) (p : Nat)
    (c r t f : Wire) (ha : acc.length=256) (hd : dirty.length=256) (hb : bits.length=255)
    (hp0 : 0<p) (hp : p<2^256) :
    (modularHalve acc dirty (true::bits) p c r t f).wires ⊆ [c,r,t,f]++acc++dirty := by
  cases acc with
  | nil => simp at ha
  | cons a rest =>
    have hs := unitary_support _ _ (doublingShift_usesOnly a f rest).adjoint
    have hc := comparison256_support (a::rest) dirty p c r t f ha hd hp0 hp
    have hk := constant256_support (a::rest) (dirty.take rest.length) bits f c r t ha
      (by simp only [List.length_take]; simp only [List.length_cons] at ha; omega) hb
    intro w hw
    simp only [modularHalve,AdaptiveCircuit.wires,modularWires_seq,List.mem_append,
      List.not_mem_nil,or_false] at hw
    rcases hw with hw | hw | hw | hw
    · simp only [circuitWires,List.flatMap_cons,List.flatMap_nil,List.append_nil,gateWires,
        List.mem_cons,List.not_mem_nil,or_false] at hw
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
      aesop

    · have h := hk hw
      simp only [List.mem_append] at h
      rcases h with (h | h) | h
      · simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
        aesop
      · simp only [List.mem_append]; aesop
      · have hm := List.mem_of_mem_take h
        simp only [List.mem_append]; aesop
    · exact hc hw
    · have h := hs hw
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
      aesop

/-- Arbitrary physical banks of width 256; all measured work remains in the same allocation. -/
theorem hornerMul256_wires_subset (controls input acc : List Wire) (bits : List Bool) (p : Nat)
    (c r t f : Wire) (hi : input.length=256) (ha : acc.length=256) (hb : bits.length=255)
    (hp0 : 0<p) (hp : p<2^256) :
    (hornerMul controls input acc (true::bits) p c r t f).wires ⊆ [c,r,t,f]++controls++input++acc := by
  induction controls with
  | nil => simp [hornerMul,AdaptiveCircuit.wires]
  | cons q qs ih =>
    have hadd := modularAdd256_support input acc bits p q c r t f hi ha hb hp0 hp
    have hdbl := double256_support acc input bits p f r t c ha hi hb hp0 hp
    simp only [List.subset_def,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ih hadd hdbl
    intro w hw
    by_cases hqs : qs=[]
    · simp only [hornerMul,modularWires_seq,hqs,if_pos] at hw
      simp only [AdaptiveCircuit.wires,List.not_mem_nil,false_or] at hw
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
      have h := hadd hw
      tauto
    · simp only [hornerMul,modularWires_seq,hqs,if_false] at hw
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
      rcases hw with hw | hw | hw
      · have h := ih hw; tauto
      · have h := hdbl hw; tauto
      · have h := hadd hw; tauto

/-- The explicit inverse retains the same banks, including its measurement corrections. -/
theorem hornerMulInverse256_wires_subset (controls input acc : List Wire) (bits : List Bool) (p : Nat)
    (c r t f : Wire) (hi : input.length=256) (ha : acc.length=256) (hb : bits.length=255)
    (hp0 : 0<p) (hp : p<2^256) :
    (hornerMulInverse controls input acc (true::bits) p c r t f).wires ⊆ [c,r,t,f]++controls++input++acc := by
  induction controls with
  | nil => simp [hornerMulInverse,AdaptiveCircuit.wires]
  | cons q qs ih =>
    have hsub := modularSub256_support input acc bits p q c r t f hi ha hb hp0 hp
    have hhalf := halve256_support acc input bits p f r t c ha hi hb hp0 hp
    simp only [List.subset_def,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ih hsub hhalf
    intro w hw
    by_cases hqs : qs=[]
    · simp only [hornerMulInverse,modularWires_seq,hqs,if_pos,AdaptiveCircuit.wires,List.not_mem_nil,or_false] at hw
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
      have h := hsub hw
      tauto
    · simp only [hornerMulInverse,modularWires_seq,hqs,if_false] at hw
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
      rcases hw with hw | hw | hw
      · have h := hsub hw; tauto
      · have h := hhalf hw; tauto
      · have h := ih hw; tauto


private theorem squareAdd256_support (input acc : List Wire) (bits : List Bool) (p : Nat)
    (q copied c r t f : Wire) (hi : input.length=256) (ha : acc.length=256) (hb : bits.length=255)
    (hp0 : 0<p) (hp : p<2^256) :
    (squareAdd input acc (true::bits) p q copied c r t f).wires ⊆ [q,copied,c,r,t,f]++input++acc := by
  have hh := modularAdd256_support input acc bits p copied c r t f hi ha hb hp0 hp
  intro w hw
  simp only [squareAdd,AdaptiveCircuit.wires,modularWires_seq,circuitWires,List.flatMap_cons,
    List.flatMap_nil,List.append_nil,gateWires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
  simp only [List.subset_def,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hh
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  rcases hw with (hw | hw) | hw | hw | hw
  · tauto
  · tauto
  · have h := hh hw; tauto
  · tauto
  · tauto
private theorem squareSub256_support (input acc : List Wire) (bits : List Bool) (p : Nat)
    (q copied c r t f : Wire) (hi : input.length=256) (ha : acc.length=256) (hb : bits.length=255)
    (hp0 : 0<p) (hp : p<2^256) :
    (squareSub input acc (true::bits) p q copied c r t f).wires ⊆ [q,copied,c,r,t,f]++input++acc := by
  have hh := modularSub256_support input acc bits p copied c r t f hi ha hb hp0 hp
  intro w hw
  simp only [squareSub,AdaptiveCircuit.wires,modularWires_seq,circuitWires,List.flatMap_cons,
    List.flatMap_nil,List.append_nil,gateWires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
  simp only [List.subset_def,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hh
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  rcases hw with (hw | hw) | hw | hw | hw
  · tauto
  · tauto
  · have h := hh hw; tauto
  · tauto
  · tauto

theorem squareLoop256_wires_subset (controls input acc : List Wire) (bits : List Bool) (p : Nat)
    (copied c r t f : Wire) (hi : input.length=256) (ha : acc.length=256) (hb : bits.length=255)
    (hp0 : 0<p) (hp : p<2^256) :
    (squareLoop controls input acc (true::bits) p copied c r t f).wires ⊆ [copied,c,r,t,f]++controls++input++acc := by
  induction controls with
  | nil => simp [squareLoop,AdaptiveCircuit.wires]
  | cons q qs ih =>
    have hadd := squareAdd256_support input acc bits p q copied c r t f hi ha hb hp0 hp
    have hdbl := double256_support acc input bits p f r t c ha hi hb hp0 hp
    simp only [List.subset_def,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ih hadd hdbl
    intro w hw
    by_cases hqs : qs=[]
    · simp only [squareLoop,modularWires_seq,hqs,if_pos] at hw
      simp only [AdaptiveCircuit.wires,List.not_mem_nil,false_or] at hw
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
      have h := hadd hw
      tauto
    · simp only [squareLoop,modularWires_seq,hqs,if_false] at hw
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
      rcases hw with hw | hw | hw
      · have h := ih hw; tauto
      · have h := hdbl hw; tauto
      · have h := hadd hw; tauto

theorem squareLoopInverse256_wires_subset (controls input acc : List Wire) (bits : List Bool) (p : Nat)
    (copied c r t f : Wire) (hi : input.length=256) (ha : acc.length=256) (hb : bits.length=255)
    (hp0 : 0<p) (hp : p<2^256) :
    (squareLoopInverse controls input acc (true::bits) p copied c r t f).wires ⊆ [copied,c,r,t,f]++controls++input++acc := by
  induction controls with
  | nil => simp [squareLoopInverse,AdaptiveCircuit.wires]
  | cons q qs ih =>
    have hsub := squareSub256_support input acc bits p q copied c r t f hi ha hb hp0 hp
    have hhalf := halve256_support acc input bits p f r t c ha hi hb hp0 hp
    simp only [List.subset_def,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ih hsub hhalf
    intro w hw
    by_cases hqs : qs=[]
    · simp only [squareLoopInverse,modularWires_seq,hqs,if_pos,AdaptiveCircuit.wires,List.not_mem_nil,or_false] at hw
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
      have h := hsub hw
      tauto
    · simp only [squareLoopInverse,modularWires_seq,hqs,if_false] at hw
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
      rcases hw with hw | hw | hw
      · have h := hsub hw; tauto
      · have h := hhalf hw; tauto
      · have h := ih hw; tauto

/-- Complete square/subtract/uncompute support on arbitrary width-256 banks. -/
theorem squareSubtract256_wires_subset (x y acc : List Wire) (correction modulus : List Bool) (p : Nat)
    (q copied c r t f : Wire) (hx : x.length=256) (hy : y.length=256) (ha : acc.length=256)
    (hc : correction.length=255) (hm : modulus.length=255) (hp0 : 0<p) (hp : p<2^256) :
    (squareSubtract x y acc (true::correction) (true::modulus) p q copied c r t f).wires ⊆
      [q,copied,c,r,t,f]++x++y++acc := by
  have hf := squareLoop256_wires_subset y y acc correction p copied c r t f hy ha hc hp0 hp
  have hr := squareLoopInverse256_wires_subset y y acc modulus p copied c r t f hy ha hm hp0 hp
  have hmid := modularSub256_support acc x modulus p q copied f r c ha hx hm hp0 hp
  simp only [List.subset_def,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hf hr hmid
  intro w hw
  simp only [squareSubtract,modularWires_seq] at hw
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  rcases hw with hw | hw | hw
  · have h := hf hw; tauto
  · have h := hmid hw; tauto
  · have h := hr hw; tauto
end ShorECDLP.Paper2607_13816
