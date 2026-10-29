import ShorECDLP.Submission.«2607_13816».Challenge.ModularPhysical
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open ShorECDLP Quantum ShorECDLP.Challenge
attribute [local irreducible] gidneyProgram uncontrolledCompareProgram

theorem constMinusProgram_wellFormed (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (q c r t : Wire) (hd : input.length=dirty.length+1) (hk : input.length=bits.length)
    (hnd : ([q,c,r,t]++input++dirty).Nodup) :
    (constMinusProgram n start input dirty bits q c r t).2.WellFormed := by
  unfold constMinusProgram
  apply prependCompiled_wellFormed
  · exact (controlledConstMinus_wellFormed input dirty bits q c r t hk hd hnd).1
  · apply appendCompiled_wellFormed
    · exact gidneyProgram_wellFormed _ _ _ _ _ _ _ _ _ hd (by simp) hnd
    · exact gidneyProgram_wellFormed _ _ _ _ _ _ _ _ _ hd hk.symm hnd

private theorem center_layout (input dirty : List Wire) (c r t iter : Wire)
    (hnd : ([c,r,t,iter] ++ input ++ dirty).Nodup) :
    ([iter,c,r,t] ++ input ++ dirty.take (input.length - 1)).Nodup := by
  have hp : ([c,r,t,iter] ++ input ++ dirty).Perm ([iter,c,r,t] ++ input ++ dirty) :=
    ((show ([c,r,t] ++ [iter]).Perm ([iter] ++ [c,r,t]) from
      List.perm_append_comm).append_right input).append_right dirty
  exact (hp.nodup_iff.mp hnd).sublist
    ((List.Sublist.refl _).append (List.take_sublist _ _))

attribute [local irreducible] constMinusProgram

theorem eeaCenterProgram_wellFormed (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t iter : Wire) (hd : input.length=dirty.length)
    (hk : input.length=bits.length) (hpos : 0 < input.length)
    (hnd : ([c,r,t,iter]++input++dirty).Nodup) :
    (eeaCenterProgram n start input dirty bits p c r t iter).2.WellFormed := by
  have ht : input.length=(dirty.take (input.length-1)).length+1 := by
    rw [List.length_take, ← hd, Nat.min_eq_left (Nat.sub_le _ _)]
    omega
  unfold eeaCenterProgram
  apply appendCompiled_wellFormed
  · exact uncontrolledCompareProgram_wellFormed _ _ _ _ _ _ _ _ _ hd hnd
  · exact constMinusProgram_wellFormed _ _ _ _ _ _ _ _ _ ht hk (center_layout input dirty c r t iter hnd)

theorem eeaUncenterProgram_wellFormed (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (p : Nat) (c r t iter : Wire) (hd : input.length=dirty.length)
    (hk : input.length=bits.length) (hpos : 0 < input.length)
    (hnd : ([c,r,t,iter]++input++dirty).Nodup) :
    (eeaUncenterProgram n start input dirty bits p c r t iter).2.WellFormed := by
  have ht : input.length=(dirty.take (input.length-1)).length+1 := by
    rw [List.length_take, ← hd, Nat.min_eq_left (Nat.sub_le _ _)]
    omega
  unfold eeaUncenterProgram
  apply appendCompiled_wellFormed
  · exact constMinusProgram_wellFormed _ _ _ _ _ _ _ _ _ ht hk (center_layout input dirty c r t iter hnd)
  · exact uncontrolledCompareProgram_wellFormed _ _ _ _ _ _ _ _ _ hd hnd
theorem eeaParityProgram_wellFormed (n start : Nat) (input dirty : List Wire) (bits : List Bool)
    (c r t iter : Wire) (hd : input.length=dirty.length+1) (hk : input.length=bits.length)
    (hnd : ([iter,c,r,t]++input++dirty).Nodup) :
    (eeaParityProgram n start input dirty bits c r t iter).2.WellFormed := by
  unfold eeaParityProgram
  apply prependCompiled_wellFormed
  · simp [CircuitWellFormed,Gate.WellFormed]
  · apply appendCompiled_wellFormed
    · exact constMinusProgram_wellFormed _ _ _ _ _ _ _ _ _ hd hk hnd
    · exact literalProgram_wellFormed _ (by simp [CircuitWellFormed,Gate.WellFormed])



theorem adaptive_seq_wellFormed_parts (first second : AdaptiveCircuit)
    (h : (first.seq second).WellFormed) : first.WellFormed ∧ second.WellFormed := by
  induction first with
  | done => exact ⟨trivial,h⟩
  | unitary gs next ih =>
    have hh := ih h.2
    exact ⟨⟨h.1,hh.1⟩,hh.2⟩
  | xMeasureReset w p q ihp ihq =>
    have hp := ihp h.1
    have hq := ihq h.2
    exact ⟨⟨hp.1,hq.1⟩,hp.2⟩

private theorem preprocessCenter_layout :
    ([560,561,562,2] ++ (List.range' 266 256).reverse ++ List.range' 4 256).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨List.nodup_append.mpr ⟨by decide,
    by simpa using (List.nodup_range' (s := 266) (n := 256)), ?_⟩,
    List.nodup_range', ?_⟩
  · intro a ha b hb he
    simp at ha hb
    rcases ha with rfl | rfl | rfl | rfl <;> omega
  · intro a ha b hb he
    simp at ha hb
    rcases ha with ha | ha
    · rcases ha with rfl | rfl | rfl | rfl; omega
    · omega

private theorem parity_layout :
    ([2,560,561,562]++List.range' 263 256++List.range' 4 255).Nodup := by
  simp only [List.nodup_append]
  refine ⟨⟨by decide,List.nodup_range',?_⟩,List.nodup_range',?_⟩
  all_goals
    intro a ha b hb he
    simp at ha hb
    omega

attribute [local irreducible] eeaCenterProgram eeaUncenterProgram eeaParityProgram
  eeaCenter eeaUncenter eeaLengthSetup eeaLengthUndo workRegistersPrepare workRegistersRestore

theorem preprocessProgram_wellFormed (n start : Nat) : (preprocessProgram n start).2.WellFormed := by
  unfold preprocessProgram
  apply surroundCompiled_wellFormed
  · exact workRegistersPrepare_resources.1
  · exact (adaptive_seq_wellFormed_parts (eeaCenter (List.range' 266 256).reverse (List.range' 4 256) (constantBits 256 (2^256-2^32-977)) (2^256-2^32-977) 560 561 562 2) (.unitary eeaLengthSetup .done) eeaPreprocess_wellFormed.2).2.1
  · exact eeaCenterProgram_wellFormed _ _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) preprocessCenter_layout

theorem unpreprocessProgram_wellFormed (n start : Nat) : (unpreprocessProgram n start).2.WellFormed := by
  unfold unpreprocessProgram
  apply surroundCompiled_wellFormed
  · exact eeaUnpreprocess_wellFormed.1
  · exact workRegistersRestore_resources.1
  · exact eeaUncenterProgram_wellFormed _ _ _ _ _ _ _ _ _ _ (by simp) (by simp) (by simp) preprocessCenter_layout

theorem productionParityProgram_wellFormed (n start : Nat) : (productionParityProgram n start).2.WellFormed := by
  unfold productionParityProgram
  exact eeaParityProgram_wellFormed _ _ _ _ _ _ _ _ _ (by simp) (by simp [secp256k1ModulusBits]) parity_layout
end ShorECDLP.Paper2607_13816.ChallengeMigration
