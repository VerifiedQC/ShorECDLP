import ShorECDLP.Submission.«2607_13816».Challenge.WindowPhysical
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge

theorem constantStraight_wellFormed {n s e : Nat} (q : Wire) (p : Straight n s e)
    (h : p.WellFormed) : (constantStraight q p).WellFormed := by
  have ht (g : TemplateGate n) (hg : g.WellFormed) : (constantTemplateGate q g).WellFormed := by
    cases g <;> exact constantControlGate_wellFormed q _ hg
  induction p with
  | done => trivial
  | gate g p ih => exact ⟨ht g h.1,ih h.2⟩
  | recordGate i v g p ih => exact ⟨constantControlGate_wellFormed q g h.1,ih h.2⟩
  | measure w p ih => exact ih h

theorem uncontrolledCompareProgram_wellFormed (n start : Nat) (input dirty : List Wire) (threshold : Nat)
    (c r t f : Wire) (hd : input.length=dirty.length)
    (hnd : ([c,r,t,f]++input++dirty).Nodup) :
    (uncontrolledCompareProgram n start input dirty threshold c r t f).2.WellFormed := by
  apply constantStraight_wellFormed
  apply compareGEProgram_wellFormed _ _ _ _ _ _ _ _ _ _ hd
  change (gidneyCompareVirtualControl input dirty c r t f :: ([c,r,t,f]++input++dirty)).Nodup
  refine List.nodup_cons.mpr ⟨?_,hnd⟩
  intro hm
  have hh : ([c,r,t,f]++input++dirty).sum+1 ≤ ([c,r,t,f]++input++dirty).sum := List.le_sum_of_mem hm
  exact (Nat.not_succ_le_self _) hh

attribute [local irreducible] uncontrolledCompareProgram gidneyProgram

theorem modularAddProgram_wellFormed (n start : Nat) (input acc : List Wire) (correction : List Bool) (p : Nat)
    (q c r t f : Wire) (hlen : input.length=acc.length) (hne : 0<acc.length)
    (hk : acc.length=correction.length) (hnd : ([q,c,r,t,f]++input++acc).Nodup) :
    (modularAddProgram n start input acc correction p q c r t f).2.WellFormed := by
  have hl := modularAdd_layout input acc q c r t f hnd
  have hd : acc.length=(input.take (acc.length-1)).length+1 := by
    rw [List.length_take,hlen,Nat.min_eq_left (Nat.sub_le _ _)]
    omega
  unfold modularAddProgram
  apply straight_append_wellFormed
  · exact literalProgram_wellFormed _ (controlledAddCarry_wellFormed input acc q c f hlen hl.1)
  · apply appendCompiled_wellFormed
    · exact uncontrolledCompareProgram_wellFormed _ _ acc input p c r t f hlen.symm hl.2.1
    · apply straight_append_wellFormed
      · exact gidneyProgram_wellFormed _ _ acc _ correction f c r t hd hk.symm hl.2.2.1
      · exact literalProgram_wellFormed _ (controlledCompareLT_wellFormed acc input q c f hlen.symm hl.2.2.2)

theorem modularSubProgram_wellFormed (n start : Nat) (input acc : List Wire) (modulus : List Bool) (p : Nat)
    (q c r t f : Wire) (hlen : input.length=acc.length) (hne : 0<acc.length)
    (hk : acc.length=modulus.length) (hnd : ([q,c,r,t,f]++input++acc).Nodup) :
    (modularSubProgram n start input acc modulus p q c r t f).2.WellFormed := by
  have hl := modularAdd_layout input acc q c r t f hnd
  have hd : acc.length=(input.take (acc.length-1)).length+1 := by
    rw [List.length_take,hlen,Nat.min_eq_left (Nat.sub_le _ _)]
    omega
  unfold modularSubProgram
  apply prependCompiled_wellFormed
  · exact controlledCompareLT_wellFormed acc input q c f hlen.symm hl.2.2.2
  · apply appendCompiled_wellFormed
    · exact gidneyProgram_wellFormed _ _ acc _ modulus f c r t hd hk.symm hl.2.2.1
    · apply appendCompiled_wellFormed
      · exact uncontrolledCompareProgram_wellFormed _ _ acc input p c r t f hlen.symm hl.2.1
      · apply literalProgram_wellFormed
        exact (circuitWellFormed_adjoint _).mpr (controlledAddCarry_wellFormed input acc q c f hlen hl.1)

theorem modularDoubleProgram_wellFormed (n start : Nat) (a : Wire) (rest dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (hk : (a::rest).length=bits.length) (hd : (a::rest).length=dirty.length)
    (hnd : ([c,r,t,f]++(a::rest)++dirty).Nodup) :
    (modularDoubleProgram n start (a::rest) dirty bits p c r t f).2.WellFormed := by
  have hl := doubling_layout (a::rest) dirty c r t f hnd
  have htlen : (a::rest).length=(dirty.take rest.length).length+1 := by
    simp only [List.length_take,List.length_cons] at hd ⊢
    rw [Nat.min_eq_left (by omega)]
  have hshort : ([f,c,r,t]++(a::rest)++dirty.take rest.length).Nodup :=
    List.Nodup.sublist ((List.Sublist.refl ([f,c,r,t]++(a::rest))).append (List.take_sublist _ _)) hl.2
  unfold modularDoubleProgram
  apply prependCompiled_wellFormed
  · exact doublingShift_wellFormed a f rest hl.1
  · apply appendCompiled_wellFormed
    · exact uncontrolledCompareProgram_wellFormed _ _ _ _ _ _ _ _ _ hd hnd
    · apply appendCompiled_wellFormed
      · exact gidneyProgram_wellFormed _ _ _ _ _ _ _ _ _ htlen hk.symm hshort
      · apply literalProgram_wellFormed
        have hfa : f≠a := fun he => (List.nodup_cons.mp hl.1).1 (by simp [he])
        simp [CircuitWellFormed,Gate.WellFormed,Ne.symm hfa]

theorem modularHalveProgram_wellFormed (n start : Nat) (a : Wire) (rest dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t f : Wire) (hk : (a::rest).length=bits.length) (hd : (a::rest).length=dirty.length)
    (hnd : ([c,r,t,f]++(a::rest)++dirty).Nodup) :
    (modularHalveProgram n start (a::rest) dirty bits p c r t f).2.WellFormed := by
  have hl := doubling_layout (a::rest) dirty c r t f hnd
  have htlen : (a::rest).length=(dirty.take rest.length).length+1 := by
    simp only [List.length_take,List.length_cons] at hd ⊢
    rw [Nat.min_eq_left (by omega)]
  have hshort : ([f,c,r,t]++(a::rest)++dirty.take rest.length).Nodup :=
    List.Nodup.sublist ((List.Sublist.refl ([f,c,r,t]++(a::rest))).append (List.take_sublist _ _)) hl.2
  unfold modularHalveProgram
  apply prependCompiled_wellFormed
  · have hfa : f≠a := fun he => (List.nodup_cons.mp hl.1).1 (by simp [he])
    simp [CircuitWellFormed,Gate.WellFormed,Ne.symm hfa]
  · apply appendCompiled_wellFormed
    · exact gidneyProgram_wellFormed _ _ _ _ _ _ _ _ _ htlen hk.symm hshort
    · apply appendCompiled_wellFormed
      · exact uncontrolledCompareProgram_wellFormed _ _ _ _ _ _ _ _ _ hd hnd
      · exact literalProgram_wellFormed _ ((circuitWellFormed_adjoint _).mpr (doublingShift_wellFormed a f rest hl.1))

attribute [local irreducible] modularAddProgram modularSubProgram modularDoubleProgram modularHalveProgram

theorem hornerProgram_wellFormed (n start : Nat) (controls input : List Wire) (a : Wire) (rest : List Wire)
    (bits : List Bool) (p : Nat) (c r t f : Wire)
    (hlen : input.length=(a::rest).length) (hk : (a::rest).length=bits.length)
    (hnd : ([c,r,t,f]++controls++input++(a::rest)).Nodup) :
    (hornerProgram n start controls input (a::rest) bits p c r t f).2.WellFormed := by
  induction controls generalizing start with
  | nil => trivial
  | cons q qs ih =>
    rw [hornerProgram]
    apply appendCompiled_wellFormed
    · exact ih _ (horner_tail_layout q qs input (a::rest) c r t f hnd)
    · let WF := fun (cp : (count : Nat) × Straight n
          (start+(hornerProgram n start qs input (a::rest) bits p c r t f).1)
          (start+(hornerProgram n start qs input (a::rest) bits p c r t f).1+count)) => cp.2.WellFormed
      change WF _
      split
      · exact modularAddProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ hlen (by simp) hk
          (horner_add_layout q qs input (a::rest) c r t f hnd)
      · apply appendCompiled_wellFormed
        · exact modularDoubleProgram_wellFormed _ _ a rest input bits p f r t c hk hlen.symm
            (horner_double_layout (q::qs) input (a::rest) c r t f hnd)
        · exact modularAddProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ hlen (by simp) hk
            (horner_add_layout q qs input (a::rest) c r t f hnd)

theorem hornerInverseProgram_wellFormed (n start : Nat) (controls input : List Wire) (a : Wire) (rest : List Wire)
    (bits : List Bool) (p : Nat) (c r t f : Wire)
    (hlen : input.length=(a::rest).length) (hk : (a::rest).length=bits.length)
    (hnd : ([c,r,t,f]++controls++input++(a::rest)).Nodup) :
    (hornerInverseProgram n start controls input (a::rest) bits p c r t f).2.WellFormed := by
  induction controls generalizing start with
  | nil => trivial
  | cons q qs ih =>
    rw [hornerInverseProgram]
    apply appendCompiled_wellFormed
    · exact modularSubProgram_wellFormed _ _ _ _ _ _ _ _ _ _ _ hlen (by simp) hk
        (horner_add_layout q qs input (a::rest) c r t f hnd)
    · let WF := fun (cp : (count : Nat) × Straight n
          (start+(modularSubProgram n start input (a::rest) bits p q c r t f).1)
          (start+(modularSubProgram n start input (a::rest) bits p q c r t f).1+count)) => cp.2.WellFormed
      change WF _
      split
      · trivial
      · apply appendCompiled_wellFormed
        · exact modularHalveProgram_wellFormed _ _ a rest input bits p f r t c hk hlen.symm
            (horner_double_layout (q::qs) input (a::rest) c r t f hnd)
        · exact ih _ (horner_tail_layout q qs input (a::rest) c r t f hnd)
end ShorECDLP.Paper2607_13816.ChallengeMigration
