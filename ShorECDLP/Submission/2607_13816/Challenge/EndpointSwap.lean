import ShorECDLP.Submission.«2607_13816».Challenge.SharedTable

namespace ShorECDLP.Paper2607_13816.ChallengeMigration

/-- The parity of the two equality tests. Equal endpoints disable the swap. -/
def endpointFlag {n : Nat} (a b x : Fin n → Bool) : Bool :=
  xor (decide (x = a)) (decide (x = b))

/-- Fixed bitwise action, with no search for the first differing bit. -/
def endpointXor {n : Nat} (a b x : Fin n → Bool) (flag : Bool) : Fin n → Bool :=
  fun i => xor (x i) (flag && xor (a i) (b i))

theorem endpointXor_swap {n : Nat} (a b x : Fin n → Bool) :
    endpointXor a b x (endpointFlag a b x) = Equiv.swap a b x := by
  by_cases ha : x = a
  · subst x
    by_cases hb : a = b
    · subst b
      simp only [endpointFlag, decide_true, Bool.xor_self, Equiv.swap_self]
      funext i
      change xor (a i) (false && xor (a i) (a i)) = a i
      cases a i <;> rfl
    · simp only [endpointFlag, decide_true, hb, decide_false, Bool.xor_false,
        Equiv.swap_apply_left]
      funext i
      unfold endpointXor
      cases a i <;> cases b i <;> rfl
  · by_cases hb : x = b
    · subst x
      simp only [endpointFlag, ha, decide_false, decide_true, Bool.false_xor,
        Equiv.swap_apply_right]
      funext i
      unfold endpointXor
      cases a i <;> cases b i <;> rfl
    · rw [Equiv.swap_apply_of_ne_of_ne ha hb]
      simp only [endpointFlag, ha, hb, decide_false, Bool.xor_self]
      funext i
      unfold endpointXor
      cases x i <;> rfl

theorem endpointFlag_swap {n : Nat} (a b x : Fin n → Bool) :
    endpointFlag a b (Equiv.swap a b x) = endpointFlag a b x := by
  by_cases ha : x = a
  · subst x
    by_cases hb : a = b
    · subst b; simp [endpointFlag]
    · simp [endpointFlag, hb, Ne.symm hb, Bool.xor_comm]
  · by_cases hb : x = b
    · subst x
      simp [endpointFlag, ha, Ne.symm ha, Bool.xor_comm]
    · rw [Equiv.swap_apply_of_ne_of_ne ha hb]

/-- Repeating the equality tests after the word update clears the flag. -/
theorem endpointFlag_uncompute {n : Nat} (a b x : Fin n → Bool) :
    xor (endpointFlag a b x)
      (endpointFlag a b (endpointXor a b x (endpointFlag a b x))) = false := by
  rw [endpointXor_swap, endpointFlag_swap]
  exact Bool.xor_self _

open ShorECDLP

/-- Two fixed Toffoli slots implement one controlled endpoint-XOR bit. -/
def endpointBitCircuit (flag a b target : Wire) : Circuit :=
  [.CCX flag a target, .CCX flag b target]

theorem endpointBitCircuit_run (flag a b target : Wire) (st : BasisState)
    (hf : flag ≠ target) (hb : b ≠ target) :
    Classical.run (endpointBitCircuit flag a b target) st =
      st[target ↦ xor (st target) (st flag && xor (st a) (st b))] := by
  funext w
  simp only [endpointBitCircuit, Classical.run_cons, Classical.run_nil, Classical.applyGate]
  by_cases hw : w = target
  · subst w
    simp only [upd_same, upd_other _ _ _ hf, upd_other _ _ _ hb]
    cases st target <;> cases st flag <;> cases st a <;> cases st b <;> rfl
  · simp [upd_other _ _ _ hw]

theorem endpointBitCircuit_HPFree (flag a b target : Wire) :
    Classical.HPFree (endpointBitCircuit flag a b target) := by
  simp [endpointBitCircuit]


/-- The endpoint input ports may alias each other, but not any modified word bit. -/
def endpointSeparated (flag : Wire) (cells : List (Wire × Wire × Wire)) : Prop :=
  ∀ c ∈ cells, flag ≠ c.2.2 ∧ ∀ d ∈ cells, d.1 ≠ c.2.2 ∧ d.2.1 ≠ c.2.2

def endpointWordCircuit (flag : Wire) (cells : List (Wire × Wire × Wire)) : Circuit :=
  cells.flatMap fun c => endpointBitCircuit flag c.1 c.2.1 c.2.2

theorem endpointWordCircuit_frame (flag : Wire) (cells : List (Wire × Wire × Wire))
    (st : BasisState) (w : Wire) (hw : ∀ c ∈ cells, w ≠ c.2.2) :
    Classical.run (endpointWordCircuit flag cells) st w = st w := by
  induction cells generalizing st with
  | nil => rfl
  | cons c cs ih =>
    simp only [endpointWordCircuit, List.flatMap_cons, Classical.run_append]
    change Classical.run (endpointWordCircuit flag cs) (Classical.run (endpointBitCircuit flag c.1 c.2.1 c.2.2) st) w = _
    rw [ih _ (fun d hd => hw d (by simp [hd]))]
    simp only [endpointBitCircuit, Classical.run_cons, Classical.run_nil, Classical.applyGate,
      upd_other _ _ _ (hw c (by simp))]

theorem endpointWordCircuit_bit (flag : Wire) (cells : List (Wire × Wire × Wire))
    (hs : endpointSeparated flag cells) (hn : (cells.map (fun c => c.2.2)).Nodup)
    (st : BasisState) (c : Wire × Wire × Wire) (hc : c ∈ cells) :
    Classical.run (endpointWordCircuit flag cells) st c.2.2 =
      xor (st c.2.2) (st flag && xor (st c.1) (st c.2.1)) := by
  induction cells generalizing st with
  | nil => simp at hc
  | cons d ds ih =>
    have hd : d ∈ d :: ds := by simp
    have htail : endpointSeparated flag ds := by
      intro e he
      exact ⟨(hs e (by simp [he])).1, fun f hf => (hs e (by simp [he])).2 f (by simp [hf])⟩
    have hnd := List.nodup_cons.mp hn
    simp only [endpointWordCircuit, List.flatMap_cons, Classical.run_append]
    change Classical.run (endpointWordCircuit flag ds) (Classical.run (endpointBitCircuit flag d.1 d.2.1 d.2.2) st) c.2.2 = _
    rw [endpointBitCircuit_run flag d.1 d.2.1 d.2.2 st (hs d hd).1 ((hs d hd).2 d hd).2]
    rcases List.mem_cons.mp hc with hcd | hc
    · subst c
      rw [endpointWordCircuit_frame]
      · exact upd_same _ _ _
      · intro e he heq
        exact hnd.1 (List.mem_map.mpr ⟨e, he, heq.symm⟩)
    · rw [ih htail hnd.2 _ hc]
      have ht : c.2.2 ≠ d.2.2 := by
        intro heq
        exact hnd.1 (List.mem_map.mpr ⟨c, hc, heq⟩)
      have ha := ((hs d hd).2 c (by simp [hc])).1
      have hb := ((hs d hd).2 c (by simp [hc])).2
      simp only [upd_other _ _ _ ht, upd_other _ _ _ (hs d hd).1,
        upd_other _ _ _ ha, upd_other _ _ _ hb]


theorem endpointWordCircuit_HPFree (flag : Wire) (cells : List (Wire × Wire × Wire)) :
    Classical.HPFree (endpointWordCircuit flag cells) := by
  induction cells with
  | nil => simp [endpointWordCircuit]
  | cons c cs ih =>
    simpa only [endpointWordCircuit, List.flatMap_cons, Classical.hpFree_append]
      using And.intro (endpointBitCircuit_HPFree flag c.1 c.2.1 c.2.2) ih

theorem endpointWordCircuit_wellFormed (flag : Wire) (cells : List (Wire × Wire × Wire))
    (hs : endpointSeparated flag cells)
    (hf : ∀ c ∈ cells, flag ≠ c.1 ∧ flag ≠ c.2.1) :
    CircuitWellFormed (endpointWordCircuit flag cells) := by
  intro g hg
  obtain ⟨c, hc, hg⟩ := List.mem_flatMap.mp hg
  have h := hs c hc
  rcases List.mem_cons.mp hg with rfl | hg
  · exact ⟨(hf c hc).1, h.1, (h.2 c hc).1⟩
  · have he : g = .CCX flag c.2.1 c.2.2 := by simpa [endpointBitCircuit] using hg
    subst g
    exact ⟨(hf c hc).2, h.1, (h.2 c hc).2⟩

theorem endpointWordCircuit_length (flag : Wire) (cells : List (Wire × Wire × Wire)) :
    (endpointWordCircuit flag cells).length = 2 * cells.length := by
  induction cells with
  | nil => rfl
  | cons c cs ih =>
    simp only [endpointWordCircuit, List.flatMap_cons, List.length_append] at *
    simpa [endpointBitCircuit, Nat.mul_add, Nat.add_comm] using ih

theorem endpointWordCircuit_tCount (flag : Wire) (cells : List (Wire × Wire × Wire)) :
    tCount (endpointWordCircuit flag cells) = 14 * cells.length := by
  induction cells with
  | nil => rfl
  | cons c cs ih =>
    simp only [endpointWordCircuit, List.flatMap_cons, tCount_append] at *
    simpa [endpointBitCircuit, tCount, tCost, Nat.mul_add, Nat.add_comm] using ih


/-- With the computed equality parity, the fixed word update is the endpoint transposition. -/
theorem endpointWordCircuit_swap {n : Nat} (flag : Wire)
    (a b target : Fin n → Wire) (st : BasisState)
    (hs : endpointSeparated flag (List.ofFn fun i => (a i, b i, target i)))
    (ht : Function.Injective target)
    (hf : st flag = endpointFlag (st ∘ a) (st ∘ b) (st ∘ target)) :
    (fun i => Classical.run (endpointWordCircuit flag
      (List.ofFn fun j => (a j, b j, target j))) st (target i)) =
      Equiv.swap (st ∘ a) (st ∘ b) (st ∘ target) := by
  funext i
  have hn : ((List.ofFn fun j => (a j, b j, target j)).map (fun c => c.2.2)).Nodup := by
    rw [List.map_ofFn]
    exact List.nodup_ofFn.mpr ht
  have hc : (a i, b i, target i) ∈ List.ofFn (fun j => (a j, b j, target j)) :=
    List.mem_ofFn.mpr ⟨i, rfl⟩
  rw [endpointWordCircuit_bit flag _ hs hn st _ hc, hf]
  exact congrFun (endpointXor_swap (st ∘ a) (st ∘ b) (st ∘ target)) i

end ShorECDLP.Paper2607_13816.ChallengeMigration
