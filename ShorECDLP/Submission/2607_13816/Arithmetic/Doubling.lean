import ShorECDLP.Submission.«2607_13816».Arithmetic.ModularAdd

/-!
# Measured modular doubling

The source extracts the top bit, rotates the word, clears its new low bit,
compares with the modulus, conditionally adds the reduction constant, and uses
odd-modulus parity to erase the reduction flag.
-/
namespace ShorECDLP.Paper2607_13816
open Classical
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

private def doublingSwap (a b : Wire) : Circuit := [.CX a b,.CX b a,.CX a b]

private theorem doublingSwap_run (a b : Wire) (s : BasisState) (hab : a ≠ b) :
    run (doublingSwap a b) s = upd (upd s a (s b)) b (s a) := by
  funext w
  by_cases ha : w = a
  · subst w; cases hsa : s a <;> cases hsb : s b <;>
      simp [doublingSwap,run,applyGate,upd,hab,Ne.symm hab,hsa,hsb]
  · by_cases hb : w = b
    · subst w; cases hsa : s a <;> cases hsb : s b <;>
        simp [doublingSwap,run,applyGate,upd,hab,Ne.symm hab,hsa,hsb]
    · simp [doublingSwap,run,applyGate,upd,ha,hb]

private theorem doublingSwap_moveCX (a b f : Wire) (s : BasisState)
    (hab : a ≠ b) (hfa : f ≠ a) (hfb : f ≠ b) :
    run (doublingSwap a b ++ [.CX f a]) s =
      run (doublingSwap a b) (run [.CX f b] s) := by
  rw [run_append,doublingSwap_run,doublingSwap_run]
  · funext w
    by_cases ha : w = a
    · subst w; simp [run,applyGate,upd,hab,Ne.symm hab,hfa,hfb]
    · by_cases hb : w = b
      · subst w; simp [run,applyGate,upd,hab,Ne.symm hab,hfa,hfb]
      · simp [run,applyGate,upd,ha,hb]
  all_goals assumption

/-- The literal descending adjacent-swap sequence in `append_cyclic_left_shift`. -/
def doublingRotate : List Wire → Circuit
  | [] => []
  | [_] => []
  | a :: b :: rest => doublingRotate (b :: rest) ++ doublingSwap a b

/-- Extract the high bit into a clean flag, then perform a logical left shift. -/
def doublingShift (acc : List Wire) (f : Wire) : Circuit :=
  match acc with
  | [] => []
  | a :: rest => [.CX ((a :: rest).getLastD a) f] ++
      doublingRotate (a :: rest) ++ [.CX f a]

private theorem doublingShift_step (a b f : Wire) (rest : List Wire) (s : BasisState)
    (hab : a ≠ b) (hfa : f ≠ a) (hfb : f ≠ b) :
    run (doublingShift (a :: b :: rest) f) s =
      run (doublingSwap a b) (run (doublingShift (b :: rest) f) s) := by
  simp only [doublingShift,doublingRotate]
  simp only [List.getLastD_cons]
  simp only [run_append]
  exact doublingSwap_moveCX a b f _ hab hfa hfb

private theorem doublingShift_values (a f : Wire) (rest : List Wire) (s : BasisState)
    (hnd : (f :: a :: rest).Nodup) (hf : s f = false) :
    wireValues (a :: rest) (run (doublingShift (a :: rest) f) s) =
      false :: (wireValues (a :: rest) s).dropLast ∧
    run (doublingShift (a :: rest) f) s f = (wireValues (a :: rest) s).getLastD false ∧
    ∀ w, w ∉ f :: a :: rest → run (doublingShift (a :: rest) f) s w = s w := by
  induction rest generalizing a s with
  | nil =>
      have hfa : f ≠ a := by simpa using (List.nodup_cons.mp hnd).1
      constructor
      · cases ha : s a <;> simp [doublingShift,doublingRotate,run,applyGate,upd,wireValues,hfa,Ne.symm hfa,hf,ha]
      constructor
      · simp [doublingShift,doublingRotate,run,applyGate,upd,wireValues,hfa,Ne.symm hfa,hf]
      · intro w hw
        simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hw
        simp [doublingShift,doublingRotate,run,applyGate,upd,hw.1,hw.2]
  | cons b rest ih =>
      have hfa : f ≠ a := by simp_all
      have hfb : f ≠ b := by simp_all
      have hab : a ≠ b := by simp_all
      have htail : (f :: b :: rest).Nodup := by simp_all
      have hh := ih b s htail hf
      let mid := run (doublingShift (b :: rest) f) s
      have hma : mid a = s a := hh.2.2 a (by
        rw [List.mem_cons,not_or]
        exact ⟨Ne.symm hfa,(List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1⟩)
      have hmb : mid b = false := by
        have h := congrArg (fun xs => xs.headD false) hh.1
        simpa only [wireValues,List.map_cons,List.headD_cons] using h
      have hrest : wireValues rest mid = (wireValues (b :: rest) s).dropLast := by
        have h := congrArg List.tail hh.1
        simpa only [wireValues,List.map_cons,List.tail_cons] using h
      rw [doublingShift_step a b f rest s hab hfa hfb,doublingSwap_run a b mid hab]
      have hvalues : wireValues rest (upd (upd mid a (mid b)) b (mid a)) = wireValues rest mid := by
        apply List.map_congr_left
        intro w hw
        have hwa : w ≠ a := by intro he; subst w; simp_all
        have hwb : w ≠ b := by intro he; subst w; simp_all
        simp [upd,hwa,hwb]
      constructor
      · change upd (upd mid a (mid b)) b (mid a) a ::
          upd (upd mid a (mid b)) b (mid a) b :: wireValues rest _ = _
        rw [hvalues,hrest]
        simp [upd,hab,hma,hmb,wireValues]
      constructor
      · simp only [upd,if_neg hfa,if_neg hfb]
        exact hh.2.1.trans (by simp [wireValues])
      · intro w hw
        have hwa : w ≠ a := by intro he; subst w; simp_all
        have hwb : w ≠ b := by intro he; subst w; simp_all
        simp only [upd,if_neg hwa,if_neg hwb]
        exact hh.2.2 w (by simp_all)

private theorem doublingWord_conservation (a : Bool) (rest : List Bool) :
    boolWordToNat (false :: (a :: rest).dropLast) +
      2 ^ (a :: rest).length * ((a :: rest).getLastD false).toNat = 2 * boolWordToNat (a :: rest) := by
  induction rest generalizing a with
  | nil => cases a <;> simp [boolWordToNat]
  | cons b rest ih =>
      have h := ih b
      simp only [List.dropLast_cons₂,List.length_cons,pow_succ,boolWordToNat,
        Bool.toNat_false,Nat.zero_add,List.getLastD_cons] at h ⊢
      nlinarith

private theorem doublingWord_value (a : Bool) (rest : List Bool) :
    boolWordToNat (false :: (a :: rest).dropLast) =
      (2 * boolWordToNat (a :: rest)) % 2 ^ (a :: rest).length ∧
    (a :: rest).getLastD false = decide (2 ^ (a :: rest).length ≤ 2 * boolWordToNat (a :: rest)) := by
  have h := doublingWord_conservation a rest
  have hlo := boolWordToNat_lt_pow_two (false :: (a :: rest).dropLast)
  have hl : (false :: (a :: rest).dropLast).length = (a :: rest).length := by simp
  rw [hl] at hlo
  constructor
  · have hm := congrArg (fun x => x % 2 ^ (a :: rest).length) h
    simpa only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hlo] using hm
  · cases hb : (a :: rest).getLastD false <;> simp only [hb,Bool.toNat_false,Bool.toNat_true,
      Nat.mul_zero,Nat.mul_one,Nat.add_zero] at h ⊢
    · exact (decide_eq_false (by omega)).symm
    · exact (decide_eq_true (by omega)).symm

/-- The emitted prefix shifts left modulo the word width, records overflow,
and changes no wire outside the word and flag. -/
theorem doublingShift_correct (a f : Wire) (rest : List Wire) (s : BasisState)
    (hnd : (f :: a :: rest).Nodup) (hf : s f = false) :
    boolWordToNat (wireValues (a :: rest) (run (doublingShift (a :: rest) f) s)) =
      (2 * boolWordToNat (wireValues (a :: rest) s)) % 2 ^ (a :: rest).length ∧
    run (doublingShift (a :: rest) f) s f =
      decide (2 ^ (a :: rest).length ≤ 2 * boolWordToNat (wireValues (a :: rest) s)) ∧
    ∀ w, w ∉ f :: a :: rest → run (doublingShift (a :: rest) f) s w = s w := by
  have hs := doublingShift_values a f rest s hnd hf
  have hv := doublingWord_value (s a) (wireValues rest s)
  rw [hs.1]
  refine ⟨?_,hs.2.1.trans ?_,hs.2.2⟩
  · simpa only [wireValues,List.map_cons,List.length_cons,List.length_map] using hv.1
  · simpa only [wireValues,List.map_cons,List.length_cons,List.length_map] using hv.2

private theorem doublingRotate_usesOnly (acc : List Wire) : PaperCircuitUsesOnly acc (doublingRotate acc) := by
  induction acc with
  | nil => simp [doublingRotate,PaperCircuitUsesOnly]
  | cons a tail ih =>
    cases tail with
    | nil => simp [doublingRotate,PaperCircuitUsesOnly]
    | cons b rest =>
      intro g hg w hw
      simp only [doublingRotate,List.mem_append] at hg
      rcases hg with hg | hg
      · exact List.mem_cons_of_mem a (ih g hg w hw)
      · simp only [doublingSwap,List.mem_cons,List.not_mem_nil,or_false] at hg
        rcases hg with rfl | rfl | rfl <;> simp_all [gateWires] <;> tauto

private theorem doublingRotate_wellFormed (acc : List Wire) (hnd : acc.Nodup) : CircuitWellFormed (doublingRotate acc) := by
  induction acc with
  | nil => simp [doublingRotate,CircuitWellFormed]
  | cons a tail ih =>
    cases tail with
    | nil => simp [doublingRotate,CircuitWellFormed]
    | cons b rest =>
      have hab : a ≠ b := by simp_all
      rw [doublingRotate,circuitWellFormed_append]
      exact ⟨ih (List.nodup_cons.mp hnd).2,by simp [doublingSwap,CircuitWellFormed,Gate.WellFormed,hab,Ne.symm hab]⟩

private theorem doublingRotate_HPFree (acc : List Wire) : HPFree (doublingRotate acc) := by
  induction acc with
  | nil => simp [doublingRotate]
  | cons a tail ih => cases tail <;> simp_all [doublingRotate,doublingSwap]

theorem doublingShift_HPFree (acc : List Wire) (f : Wire) : HPFree (doublingShift acc f) := by
  cases acc <;> simp [doublingShift,doublingRotate_HPFree]

theorem doublingShift_wellFormed (a f : Wire) (rest : List Wire)
    (hnd : (f :: a :: rest).Nodup) : CircuitWellFormed (doublingShift (a :: rest) f) := by
  have hfa : f ≠ a := by simp_all
  have hlast : (a :: rest).getLastD a ∈ a :: rest := by
    simpa only [List.getLastD_cons] using (List.getLastD_mem_cons (l := rest) (a := a))
  have hfl : f ≠ (a :: rest).getLastD a := by
    intro he; rw [← he] at hlast; exact (List.nodup_cons.mp hnd).1 hlast
  simp only [doublingShift,circuitWellFormed_append]
  exact ⟨⟨by
      intro g hg; have he := List.mem_singleton.mp hg; subst g; exact Ne.symm hfl,
    doublingRotate_wellFormed _ (List.nodup_cons.mp hnd).2⟩,by simp [CircuitWellFormed,Gate.WellFormed,hfa]⟩

/-- Literal source modular doubling, using the low-bit parity to clear the flag. -/
def modularDouble (acc dirty : List Wire) (correction : List Bool) (p : Nat) (c r t f : Wire) : Quantum.AdaptiveCircuit :=
  match acc with
  | [] => .done
  | a :: rest => .unitary (doublingShift (a :: rest) f)
      ((gidneyCompareGE (a :: rest) dirty p c r t f).seq
        ((controlledGidneyAddConst (a :: rest) (dirty.take rest.length) correction f c r t).seq
          (.unitary [.CX a f] .done)))

/-- Shared layouts for measured doubling and halving. -/
theorem doubling_layout (acc dirty : List Wire) (c r t f : Wire)
    (hnd : ([c,r,t,f] ++ acc ++ dirty).Nodup) :
    (f :: acc).Nodup ∧ ([f,c,r,t] ++ acc ++ dirty).Nodup := by
  have hp : ([f,c,r,t] ++ acc ++ dirty).Perm ([c,r,t,f] ++ acc ++ dirty) := by
    have h : ([f,c,r,t] : List Wire).Perm [c,r,t,f] :=
      List.perm_append_comm (l₁ := [f]) (l₂ := [c,r,t])
    exact (h.append_right acc).append_right dirty
  have hh := hp.nodup_iff.mpr hnd
  constructor
  · have ha := (List.nodup_append.mp hnd).1
    have hb := (List.nodup_append.mp ha).2.1
    have hf : f ∉ acc := by
      intro h
      exact (List.nodup_append.mp ha).2.2 f (by simp) f h rfl
    exact List.nodup_cons.mpr ⟨hf,hb⟩
  · exact hh

private def doublingLow (acc : List Wire) (f : Wire) (s : BasisState) : BasisState := run (doublingShift acc f) s
private def doublingFlagged (acc : List Wire) (p : Nat) (f : Wire) (s : BasisState) : BasisState :=
  let low := doublingLow acc f s
  upd low f (Bool.xor (low f) (decide (p ≤ boolWordToNat (wireValues acc low))))

/-- The canonical doubled residue with the reduction flag restored. -/
def modularDoubleIdealState (acc : List Wire) (correction : List Bool) (p : Nat) (f : Wire) (s : BasisState) : BasisState :=
  upd (gidneyAddIdealState acc correction f (doublingFlagged acc p f s)) f (s f)

private theorem doubling_intermediate_frame (a f : Wire) (rest : List Wire) (correction : List Bool)
    (p : Nat) (s : BasisState) (hnd : (f :: a :: rest).Nodup) (hf : s f = false)
    (hk : (a :: rest).length = correction.length) :
    (∀ w, w ∉ f :: a :: rest → doublingLow (a :: rest) f s w = s w) ∧
    (∀ w, w ∉ f :: a :: rest → doublingFlagged (a :: rest) p f s w = s w) ∧
    (∀ w, w ∉ f :: a :: rest →
      gidneyAddIdealState (a :: rest) correction f (doublingFlagged (a :: rest) p f s) w = s w) := by
  have hl := (doublingShift_correct a f rest s hnd hf).2.2
  have hflag : ∀ w, w ∉ f :: a :: rest → doublingFlagged (a :: rest) p f s w = s w := by
    intro w hw
    have hwf : w ≠ f := fun he => hw (by simp [he])
    simp only [doublingFlagged,upd,if_neg hwf]
    exact hl w hw
  refine ⟨hl,hflag,?_⟩
  intro w hw
  have hwa : w ∉ a :: rest := fun h => hw (List.mem_cons_of_mem f h)
  exact ((gidneyAddIdealState_correct (a :: rest) correction f _ hk (List.nodup_cons.mp hnd).2).2 w hwa).trans (hflag w hw)

private theorem doubling_word_upd (ws : List Wire) (s : BasisState) (f : Wire) (b : Bool) (hf : f ∉ ws) :
    wireValues ws (upd s f b) = wireValues ws s := by
  apply List.map_congr_left
  intro w hw
  have hn : w ≠ f := by intro he; subst w; exact hf hw
  simp [upd,hn]

private theorem doubling_corrected (a f : Wire) (rest : List Wire) (correction : List Bool)
    (p : Nat) (s : BasisState) (hnd : (f :: a :: rest).Nodup) (hf : s f = false)
    (hk : (a :: rest).length = correction.length) (hp : p < 2 ^ (a :: rest).length)
    (hx : boolWordToNat (wireValues (a :: rest) s) < p) (hodd : p % 2 = 1)
    (hconstant : boolWordToNat correction = 2 ^ (a :: rest).length - p) :
    let mid := gidneyAddIdealState (a :: rest) correction f (doublingFlagged (a :: rest) p f s)
    boolWordToNat (wireValues (a :: rest) mid) = (2 * boolWordToNat (wireValues (a :: rest) s)) % p ∧
    run [.CX a f] mid = modularDoubleIdealState (a :: rest) correction p f s := by
  let acc := a :: rest
  let x := boolWordToNat (wireValues acc s)
  let flagged := doublingFlagged acc p f s
  let mid := gidneyAddIdealState acc correction f flagged
  have hn := (List.nodup_cons.mp hnd).1
  have hs := doublingShift_correct a f rest s hnd hf
  have hflagword : boolWordToNat (wireValues acc flagged) = (2 * x) % 2 ^ acc.length := by
    unfold flagged doublingFlagged
    rw [doubling_word_upd _ _ _ _ hn]
    exact hs.1
  have hflag : flagged f = Bool.xor (decide (2 ^ acc.length ≤ 2*x)) (decide (p ≤ (2*x) % 2 ^ acc.length)) := by
    simp only [flagged,doublingFlagged,upd,↓reduceIte]
    change Bool.xor (run (doublingShift acc f) s f)
      (decide (p ≤ boolWordToNat (wireValues acc (run (doublingShift acc f) s)))) = _
    rw [hs.1,hs.2.1]
  have hmath := modularCorrection_correct (2 ^ acc.length) p x x true hp hx hx
  have hred := modularCorrection_flag (2 ^ acc.length) p x x true hp hx hx
  simp only [↓reduceIte,← Nat.two_mul] at hmath hred
  have hadd := gidneyAddIdealState_correct acc correction f flagged hk (List.nodup_cons.mp hnd).2
  have hvalue : boolWordToNat (wireValues acc mid) = (2*x) % p := by
    rw [hadd.1,hflagword,hflag,hconstant]
    exact hmath.1
  have hmidflag : mid f = decide (p ≤ 2*x) := by
    exact (hadd.2 f hn).trans (hflag.trans hred)
  have hbit : mid a = decide (boolWordToNat (wireValues acc mid) % 2 = 1) := by
    cases hb : mid a <;> simp [acc,wireValues,boolWordToNat,hb,Nat.add_mod]
  refine ⟨hvalue,?_⟩
  change upd mid f (Bool.xor (mid f) (mid a)) = upd mid f (s f)
  rw [hmidflag,hbit,hvalue,modularDoubling_cleanup p x hodd hx,hf,Bool.xor_self]

/-- Undoing the parity CNOT and adding the modulus restores the flagged shift
state. This is the first half of the source halving circuit. -/
theorem modularDoubleIdealState_uncorrect (a f : Wire) (rest : List Wire)
    (correction modulus : List Bool) (p : Nat) (s : BasisState)
    (hnd : (f :: a :: rest).Nodup) (hf : s f = false)
    (hk : (a :: rest).length = correction.length) (hm : (a :: rest).length = modulus.length)
    (hp : p < 2 ^ (a :: rest).length)
    (hx : boolWordToNat (wireValues (a :: rest) s) < p) (hodd : p % 2 = 1)
    (hconstant : boolWordToNat correction = 2 ^ (a :: rest).length - p)
    (hmodulus : boolWordToNat modulus = p) :
    gidneyAddIdealState (a :: rest) modulus f
      (run [.CX a f] (modularDoubleIdealState (a :: rest) correction p f s)) =
      let low := run (doublingShift (a :: rest) f) s
      upd low f (Bool.xor (low f) (decide (p ≤ boolWordToNat (wireValues (a :: rest) low)))) := by
  have hn := (List.nodup_cons.mp hnd).1
  have hfa : f ≠ a := by intro he; exact hn (by simp [he])
  have hlast := (doubling_corrected a f rest correction p s hnd hf hk hp hx hodd hconstant).2
  have hinv (z : BasisState) : run ([.CX a f] : Circuit) (run [.CX a f] z) = z := by
    funext w
    by_cases hw : w = f <;> simp [run,applyGate,upd,hw,Ne.symm hfa,Bool.xor_assoc]
  rw [← hlast,hinv]
  exact gidneyAddIdealState_complement (a :: rest) correction modulus f _ hk hm
    (List.nodup_cons.mp hnd).2 hn (by rw [hconstant,hmodulus]; omega)

/-- The ideal state is numeric modular doubling and preserves every other wire. -/
theorem modularDoubleIdealState_correct (a f : Wire) (rest : List Wire) (correction : List Bool)
    (p : Nat) (s : BasisState) (hnd : (f :: a :: rest).Nodup) (hf : s f = false)
    (hk : (a :: rest).length = correction.length) (hp : p < 2 ^ (a :: rest).length)
    (hx : boolWordToNat (wireValues (a :: rest) s) < p) (hodd : p % 2 = 1)
    (hconstant : boolWordToNat correction = 2 ^ (a :: rest).length - p) :
    boolWordToNat (wireValues (a :: rest) (modularDoubleIdealState (a :: rest) correction p f s)) =
      (2 * boolWordToNat (wireValues (a :: rest) s)) % p ∧
    ∀ w, w ∉ a :: rest → modularDoubleIdealState (a :: rest) correction p f s w = s w := by
  constructor
  · unfold modularDoubleIdealState
    rw [doubling_word_upd _ _ _ _ (List.nodup_cons.mp hnd).1]
    exact (doubling_corrected a f rest correction p s hnd hf hk hp hx hodd hconstant).1
  · intro w hw
    by_cases hwf : w = f
    · subst w; simp [modularDoubleIdealState,upd]
    · simp only [modularDoubleIdealState,upd,if_neg hwf]
      exact (doubling_intermediate_frame a f rest correction p s hnd hf hk).2.2 w (by simp [hwf,hw])

private theorem doubling_add_layout (acc dirty : List Wire) (c r t f : Wire) (n : Nat)
    (hnd : ([c,r,t,f] ++ acc ++ dirty).Nodup) :
    ([f,c,r,t] ++ acc ++ dirty.take n).Nodup :=
  List.Nodup.sublist ((List.take_sublist n dirty).append_left ([f,c,r,t] ++ acc))
    (doubling_layout acc dirty c r t f hnd).2

/-- All gates and all measurement branches are well formed in the shared layout. -/
theorem modularDouble_wellFormed (a : Wire) (rest dirty : List Wire) (correction : List Bool)
    (p : Nat) (c r t f : Wire) (hk : (a :: rest).length = correction.length)
    (hd : (a :: rest).length = dirty.length)
    (hnd : ([c,r,t,f] ++ (a :: rest) ++ dirty).Nodup) :
    (modularDouble (a :: rest) dirty correction p c r t f).WellFormed := by
  have hl := (doubling_layout (a :: rest) dirty c r t f hnd).1
  have htlen : (a :: rest).length = (dirty.take rest.length).length + 1 := by
    simp only [List.length_take,List.length_cons] at hd ⊢
    rw [Nat.min_eq_left (by omega)]
  refine ⟨doublingShift_wellFormed a f rest hl,?_⟩
  apply Quantum.AdaptiveCircuit.WellFormed.seq
  · exact gidneyCompareGE_wellFormed _ _ _ _ _ _ _ hd hnd
  · apply Quantum.AdaptiveCircuit.WellFormed.seq
    · exact controlledGidneyAddConst_wellFormed _ _ _ _ _ _ _ hk htlen
        (doubling_add_layout (a :: rest) dirty c r t f rest.length hnd)
    · refine ⟨?_,True.intro⟩
      have hfa : f ≠ a := fun he => (List.nodup_cons.mp hl).1 (by simp [he])
      simp [CircuitWellFormed,Gate.WellFormed,Ne.symm hfa]

private theorem doubling_clean_geometry (a : Wire) (rest dirty : List Wire) (c r t f : Wire)
    (hnd : ([c,r,t,f] ++ (a :: rest) ++ dirty).Nodup) :
    ∀ w ∈ [c,r,t], w ∉ f :: a :: rest := by
  intro w hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl <;> simp_all

/-- Each branch doubles modulo the odd modulus with a positive input-independent
amplitude. The reduction flag and every borrowed or clean wire are restored. -/
theorem modularDouble_branch_correct (a : Wire) (rest dirty : List Wire) (correction : List Bool)
    (p : Nat) (c r t f : Wire) (s : BasisState) (hk : (a :: rest).length = correction.length)
    (hd : (a :: rest).length = dirty.length) (hnd : ([c,r,t,f] ++ (a :: rest) ++ dirty).Nodup)
    (hc : s c = false) (hr : s r = false) (ht : s t = false) (hf : s f = false)
    (hp : p < 2 ^ (a :: rest).length) (hx : boolWordToNat (wireValues (a :: rest) s) < p)
    (hodd : p % 2 = 1) (hconstant : boolWordToNat correction = 2 ^ (a :: rest).length - p)
    (branch : Quantum.InstrumentBranch) (hb : branch ∈ (modularDouble (a :: rest) dirty correction p c r t f).run) :
    let m := (a :: rest).length + if correction.all (fun k => !k) then 0 else (dirty.take rest.length).length
    branch.history.length = m ∧ branch.kraus (Quantum.ket s) = Quantum.registerXResetMagnitude m •
      Quantum.ket (modularDoubleIdealState (a :: rest) correction p f s) := by
  have hl := (doubling_layout (a :: rest) dirty c r t f hnd).1
  have hg := doubling_clean_geometry a rest dirty c r t f hnd
  have hframe := doubling_intermediate_frame a f rest correction p s hl hf hk
  have htlen : (a :: rest).length = (dirty.take rest.length).length + 1 := by
    simp only [List.length_take,List.length_cons] at hd ⊢
    rw [Nat.min_eq_left (by omega)]
  obtain ⟨after,ha,hh,hbranch⟩ := gidneyUnitaryBranch (doublingShift (a :: rest) f) _ branch hb
  simp only [Quantum.AdaptiveCircuit.run_seq,Quantum.Instrument.seq,List.mem_flatMap,List.mem_map,
    Quantum.AdaptiveCircuit.run_unitary_done,List.mem_singleton] at ha
  obtain ⟨compareBranch,hcompare,addTail,haddTail,rfl⟩ := ha
  obtain ⟨addBranch,haddBranch,last,rfl,rfl⟩ := haddTail
  have hshort : ¬ (p = 0 ∨ 2 ^ (a :: rest).length ≤ p) := by omega
  have hcmp := gidneyCompareGE_branch_correct (a :: rest) dirty p c r t f (doublingLow (a :: rest) f s)
    hd hnd ((hframe.1 c (hg c (by simp))).trans hc) ((hframe.1 r (hg r (by simp))).trans hr)
    ((hframe.1 t (hg t (by simp))).trans ht) compareBranch hcompare
  simp only [if_neg hshort] at hcmp
  have hadd := controlledGidneyAddConst_branch_correct (a :: rest) (dirty.take rest.length) correction f c r t
    (doublingFlagged (a :: rest) p f s) hk htlen (doubling_add_layout (a :: rest) dirty c r t f rest.length hnd)
    ((hframe.2.1 c (hg c (by simp))).trans hc) ((hframe.2.1 r (hg r (by simp))).trans hr)
    ((hframe.2.1 t (hg t (by simp))).trans ht) addBranch haddBranch
  have hlast := (doubling_corrected a f rest correction p s hl hf hk hp hx hodd hconstant).2
  dsimp only at hadd ⊢
  constructor
  · rw [hh]
    simp only [Quantum.InstrumentBranch.seq,List.length_append,List.length_nil,Nat.add_zero,hcmp.1,hadd.1]
  · rw [hbranch]
    simp only [Quantum.InstrumentBranch.seq,LinearMap.comp_apply]
    rw [Quantum.run_ket_agrees_classical _ _ (doublingShift_HPFree (a :: rest) f)]
    change Quantum.run [.CX a f] (addBranch.kraus (compareBranch.kraus (Quantum.ket (doublingLow (a :: rest) f s)))) = _
    rw [hcmp.2,map_smul]
    change Quantum.run [.CX a f] (Quantum.registerXResetMagnitude (a :: rest).length •
      addBranch.kraus (Quantum.ket (doublingFlagged (a :: rest) p f s))) = _
    rw [hadd.2,map_smul,map_smul,Quantum.run_ket_agrees_classical _ _ (by simp),hlast]
    simp only [smul_smul,Quantum.registerXResetMagnitude,← pow_add]

private theorem doublingRotate_counts (acc : List Wire) :
    eeaToffoliCount (doublingRotate acc) = 0 ∧
    eeaCnotCount (doublingRotate acc) = 3 * (acc.length - 1) ∧
    tCount (doublingRotate acc) = 0 := by
  induction acc with
  | nil => simp [doublingRotate,eeaToffoliCount,eeaCnotCount,tCount]
  | cons a tail ih =>
    cases tail with
    | nil => simp [doublingRotate,eeaToffoliCount,eeaCnotCount,tCount]
    | cons b rest =>
      simp only [doublingRotate,eeaToffoliCount_append,eeaCnotCount_append,tCount_append,ih.1,ih.2.1,ih.2.2]
      simp [doublingSwap,eeaToffoliCount,eeaCnotCount,tCount,tCost]
      omega

theorem doublingShift_counts (a f : Wire) (rest : List Wire) :
    eeaToffoliCount (doublingShift (a :: rest) f) = 0 ∧
    eeaCnotCount (doublingShift (a :: rest) f) = 3 * rest.length + 2 ∧
    tCount (doublingShift (a :: rest) f) = 0 := by
  simp only [doublingShift,eeaToffoliCount_append,eeaCnotCount_append,tCount_append,
    (doublingRotate_counts (a :: rest)).1,(doublingRotate_counts (a :: rest)).2.1,
    (doublingRotate_counts (a :: rest)).2.2]
  simp [eeaToffoliCount,eeaCnotCount,tCount,tCost]; omega

theorem doublingShift_usesOnly (a f : Wire) (rest : List Wire) :
    PaperCircuitUsesOnly (f :: a :: rest) (doublingShift (a :: rest) f) := by
  have hlast : (a :: rest).getLastD a ∈ a :: rest := by
    simpa only [List.getLastD_cons] using (List.getLastD_mem_cons (l := rest) (a := a))
  intro g hg w hw
  simp only [doublingShift,List.mem_append,List.mem_singleton] at hg
  rcases hg with (rfl | hg) | rfl
  · simp only [gateWires,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl
    · exact List.mem_cons_of_mem f hlast
    · simp
  · exact List.mem_cons_of_mem f (doublingRotate_usesOnly (a :: rest) g hg w hw)
  · simp_all [gateWires]; tauto

/-- Production doubling in one accumulator and one borrowed word. -/
def secp256k1ModularDouble : Quantum.AdaptiveCircuit :=
  modularDouble (List.range' 4 256) (List.range' 260 256) secp256k1ReductionConstantBits
    (2 ^ 256 - (2 ^ 32 + 977)) 1 2 3 0

private theorem doublingGateCount_seq (cost : Gate → Nat) (a b : Quantum.AdaptiveCircuit) :
    gidneyGateCount cost (a.seq b) = gidneyGateCount cost a + gidneyGateCount cost b := by
  induction a with
  | done => simp [Quantum.AdaptiveCircuit.seq,gidneyGateCount]
  | unitary gates next ih => simp [Quantum.AdaptiveCircuit.seq,gidneyGateCount,ih,Nat.add_assoc]
  | xMeasureReset w l r ihl ihr =>
      simp [Quantum.AdaptiveCircuit.seq,gidneyGateCount,ihl,ihr,max_add_add_right]

private theorem doublingMeasurements_seq (a b : Quantum.AdaptiveCircuit) :
    (a.seq b).measurementCount = a.measurementCount + b.measurementCount := by
  induction a with
  | done => simp [Quantum.AdaptiveCircuit.seq,Quantum.AdaptiveCircuit.measurementCount]
  | unitary gates next ih => exact ih
  | xMeasureReset w l r ihl ihr =>
      simp [Quantum.AdaptiveCircuit.seq,Quantum.AdaptiveCircuit.measurementCount,ihl,ihr,
        max_add_add_right,Nat.add_assoc]

private theorem doublingWires_seq (a b : Quantum.AdaptiveCircuit) (w : Wire) :
    w ∈ (a.seq b).wires ↔ w ∈ a.wires ∨ w ∈ b.wires := by
  induction a with
  | done => simp [Quantum.AdaptiveCircuit.seq,Quantum.AdaptiveCircuit.wires]
  | unitary gates next ih => simp [Quantum.AdaptiveCircuit.seq,Quantum.AdaptiveCircuit.wires,ih,or_assoc]
  | xMeasureReset t l r ihl ihr =>
      simp only [Quantum.AdaptiveCircuit.seq,Quantum.AdaptiveCircuit.wires,List.mem_cons,List.mem_append,ihl,ihr]
      tauto


private def doublingProductionCompare : Quantum.AdaptiveCircuit :=
  gidneyCompareGE (List.range' 4 256) (List.range' 260 256)
    (2 ^ 256 - (2 ^ 32 + 977)) 1 2 3 0

private def doublingProductionQ : Wire :=
  ([1,2,3,0] ++ List.range' 4 256 ++ List.range' 260 256).sum + 1

set_option maxRecDepth 10000 in
private theorem doublingProduction_core : doublingProductionCompare =
    constantControlProgram doublingProductionQ
      (controlledGidneyCompareCarry (List.range' 4 256) (List.range' 260 256)
        secp256k1ReductionConstantBits doublingProductionQ 1 2 3 0) := by
  unfold doublingProductionCompare gidneyCompareGE
  dsimp only
  unfold controlledGidneyCompareGE
  rw [if_neg (by decide)]
  simp only [List.length_range']
  rw [if_neg (by decide),Nat.sub_sub_self (by decide : 2 ^ 32 + 977 ≤ 2 ^ 256)]
  rfl

private theorem doublingProduction_fresh :
    doublingProductionQ ∉ [1,2,3,0] ++ List.range' 4 256 ++ List.range' 260 256 :=
  by
    intro h
    have hh : doublingProductionQ ≤ ([1,2,3,0] ++ List.range' 4 256 ++ List.range' 260 256).sum := List.le_sum_of_mem h
    exact (Nat.not_succ_le_self (([1,2,3,0] ++ List.range' 4 256 ++ List.range' 260 256).sum)) hh


set_option maxRecDepth 100000 in
private theorem doublingProduction_compare_wires (w : Wire) :
    w ∈ doublingProductionCompare.wires ↔ w ∈ [1,2,3,0] ++ List.range' 4 256 ++ List.range' 260 256 := by
  rw [doublingProduction_core,constantControlProgram_wires _ _
    (controlledGidneyCompareCarry_controlSafe _ _ _ _ _ _ _ _ doublingProduction_fresh),
    show List.range' 4 256 = 4 :: List.range' 5 255 from rfl,
    show List.range' 260 256 = 260 :: List.range' 261 255 from rfl,
    show secp256k1ReductionConstantBits = true ::
      (List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977)) from rfl,
    controlledGidneyCompareCarry_wires _ _ _ _ _ _ _ _ _ _ (by simp) (by simp)]
  have hf := doublingProduction_fresh
  change (w ∈ doublingProductionQ :: ([1,2,3,0] ++ List.range' 4 256 ++ List.range' 260 256) ∧ w ≠ doublingProductionQ) ↔ w ∈ [1,2,3,0] ++ List.range' 4 256 ++ List.range' 260 256
  by_cases hw : w = doublingProductionQ
  · subst w; simpa only [ne_eq,not_true_eq_false,and_false,false_iff] using hf
  · simp only [List.mem_cons]
    constructor
    · intro h; exact h.1.resolve_left hw
    · intro h; exact ⟨Or.inr h,hw⟩

set_option maxRecDepth 100000 in
private theorem doublingProduction_add_wires (w : Wire) :
    w ∈ secp256k1GidneyAdd.wires ↔ w ∈ [0,1,2,3] ++ List.range' 4 256 ++ List.range' 260 255 := by
  unfold secp256k1GidneyAdd
  rw [show List.range' 4 256 = 4 :: List.range' 5 255 from rfl,
    show List.range' 260 255 = 260 :: List.range' 261 254 from rfl,
    show secp256k1ReductionConstantBits = true ::
      (List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977)) from rfl]
  exact controlledGidneyAddConst_wires _ _ _ _ _ _ _ _ _ (by simp) (by simp) w


set_option maxRecDepth 100000 in
private theorem doublingProduction_decompose : secp256k1ModularDouble =
    .unitary (doublingShift (List.range' 4 256) 0)
      (doublingProductionCompare.seq (secp256k1GidneyAdd.seq (.unitary [.CX 4 0] .done))) := by
  unfold secp256k1ModularDouble
  rw [show List.range' 4 256 = 4 :: List.range' 5 255 from rfl]
  unfold modularDouble
  dsimp only
  rw [show (List.range' 260 256).take (List.range' 5 255).length = List.range' 260 255 from rfl]
  rfl

set_option maxRecDepth 100000 in
private theorem doublingProduction_modadd : secp256k1ModularAdd =
    .unitary (controlledAddCarry (List.range' 260 256) (List.range' 4 256) 516 1 0)
      (doublingProductionCompare.seq (secp256k1GidneyAdd.seq
        (.unitary (controlledCompareLT (List.range' 4 256) (List.range' 260 256) 516 1 0) .done))) := by
  unfold secp256k1ModularAdd controlledModularAdd
  rw [show (List.range' 4 256).length - 1 = 255 from rfl,
    show (List.range' 260 256).take 255 = List.range' 260 255 from rfl]
  rfl

theorem doublingFour_counts (g h : Circuit) (a b : Quantum.AdaptiveCircuit) :
    gidneyToffoliCount (.unitary g (a.seq (b.seq (.unitary h .done)))) =
      eeaToffoliCount g + (gidneyToffoliCount a + (gidneyToffoliCount b + eeaToffoliCount h)) ∧
    gidneyCnotCount (.unitary g (a.seq (b.seq (.unitary h .done)))) =
      eeaCnotCount g + (gidneyCnotCount a + (gidneyCnotCount b + eeaCnotCount h)) ∧
    (Quantum.AdaptiveCircuit.unitary g (a.seq (b.seq (.unitary h .done)))).tCount =
      tCount g + (a.tCount + (b.tCount + tCount h)) ∧
    (Quantum.AdaptiveCircuit.unitary g (a.seq (b.seq (.unitary h .done)))).measurementCount =
      a.measurementCount + b.measurementCount := by
  constructor
  · simp only [gidneyToffoliCount,doublingGateCount_seq,gidneyGateCount,Nat.add_zero]; rfl
  constructor
  · simp only [gidneyCnotCount,doublingGateCount_seq,gidneyGateCount,Nat.add_zero]; rfl
  constructor
  · rw [← gidneyGateCount_tCount]
    simp only [doublingGateCount_seq,gidneyGateCount,gidneyGateCount_tCount,Nat.add_zero]; rfl
  · simp only [Quantum.AdaptiveCircuit.measurementCount,doublingMeasurements_seq,Nat.add_zero]

set_option maxRecDepth 100000 in
private theorem doublingProduction_counts :
    gidneyToffoliCount secp256k1ModularDouble = 1531 ∧
    gidneyCnotCount secp256k1ModularDouble = 3649 ∧
    secp256k1ModularDouble.tCount = 10717 ∧
    secp256k1ModularDouble.measurementCount = 511 := by
  have hm := (secp256k1ModularAdd_correct_resources (fun _ => false) rfl rfl rfl rfl (by decide) (by decide)).2.2.2.2.2
  have hrot := doublingShift_counts 4 0 (List.range' 5 255)
  change eeaToffoliCount (doublingShift (List.range' 4 256) 0) = 0 ∧
    eeaCnotCount (doublingShift (List.range' 4 256) 0) = 767 ∧
    tCount (doublingShift (List.range' 4 256) 0) = 0 at hrot
  have hb := controlledCompareLT_counts 4 (List.range' 5 255) (List.range' 260 256) 516 1 0 (by simp)
  change eeaToffoliCount (controlledCompareLT (List.range' 4 256) (List.range' 260 256) 516 1 0) = 513 ∧
    eeaCnotCount (controlledCompareLT (List.range' 4 256) (List.range' 260 256) 516 1 0) = 1024 ∧
    eeaXCount (controlledCompareLT (List.range' 4 256) (List.range' 260 256) 516 1 0) = 516 ∧
    tCount (controlledCompareLT (List.range' 4 256) (List.range' 260 256) 516 1 0) = 3591 at hb
  have hadd := doublingFour_counts
    (controlledAddCarry (List.range' 260 256) (List.range' 4 256) 516 1 0)
    (controlledCompareLT (List.range' 4 256) (List.range' 260 256) 516 1 0)
    doublingProductionCompare secp256k1GidneyAdd
  rw [← doublingProduction_modadd] at hadd
  have hdbl := doublingFour_counts (doublingShift (List.range' 4 256) 0) ([.CX 4 0] : Circuit)
    doublingProductionCompare secp256k1GidneyAdd
  rw [← doublingProduction_decompose] at hdbl
  have hccx := hadd.1.symm.trans hm.1
  have hcx := hadd.2.1.symm.trans hm.2.1
  have ht := hadd.2.2.1.symm.trans hm.2.2.1
  rw [controlledAddCarry_toffoliCount _ _ _ _ _ (by simp),hb.1] at hccx
  rw [controlledAddCarry_cnotCount _ _ _ _ _ (by simp),hb.2.1] at hcx
  rw [controlledAddCarry_tCount _ _ _ _ _ (by simp),hb.2.2.2] at ht
  simp only [List.length_range'] at hccx hcx ht
  refine ⟨hdbl.1.trans ?_,hdbl.2.1.trans ?_,hdbl.2.2.1.trans ?_,hdbl.2.2.2.trans (hadd.2.2.2.symm.trans hm.2.2.2.1)⟩
  · rw [hrot.1,show eeaToffoliCount ([.CX 4 0] : Circuit) = 0 from rfl]
    omega
  · rw [hrot.2.1,show eeaCnotCount ([.CX 4 0] : Circuit) = 1 from rfl]
    omega
  · rw [hrot.2.2,show tCount ([.CX 4 0] : Circuit) = 0 from rfl]
    omega

private theorem doublingProduction_wires (w : Wire) :
    w ∈ secp256k1ModularDouble.wires ↔ w ∈ List.range' 0 516 := by
  rw [doublingProduction_decompose]
  simp only [Quantum.AdaptiveCircuit.wires,List.mem_append,doublingWires_seq,
    doublingProduction_compare_wires,doublingProduction_add_wires,List.not_mem_nil,or_false]
  have hfirst := doublingShift_usesOnly 4 0 (List.range' 5 255)
  constructor
  · intro h
    rcases h with h | h | h | h
    · obtain ⟨g,hg,hw⟩ := List.mem_flatMap.mp h
      have hh := hfirst g hg w hw
      simp at hh ⊢
      dsimp only [Wire] at *
      omega
    · simp at h ⊢; dsimp only [Wire] at *; omega
    · simp at h ⊢; dsimp only [Wire] at *; omega
    · simp [circuitWires,gateWires] at h
      simp; dsimp only [Wire] at *; omega
  · intro h
    right; left
    simp at h ⊢; dsimp only [Wire] at *; omega

private theorem doublingProduction_qubits : secp256k1ModularDouble.qubitCount = 516 := by
  have heq : secp256k1ModularDouble.wires.dedup.toFinset = (List.range' 0 516).toFinset := by
    ext w; simpa only [List.mem_toFinset,List.mem_dedup] using doublingProduction_wires w
  have hc := congrArg Finset.card heq
  simpa only [List.toFinset_card_of_nodup (List.nodup_dedup _),
    List.toFinset_card_of_nodup (List.nodup_range'),List.length_range'] using hc

set_option maxHeartbeats 4000000 in
private theorem doublingProduction_layout :
    ([1,2,3,0] ++ List.range' 4 256 ++ List.range' 260 256).Nodup := by decide

/-- One concrete doubling program: canonical modular arithmetic, complete frame,
normalized quantum branches, 1,531 CCX, 3,649 CX, 10,717 T, 511 resets and 516 wires. -/
theorem secp256k1ModularDouble_correct_resources (s : BasisState)
    (hc : s 1 = false) (hr : s 2 = false) (ht : s 3 = false) (hf : s 0 = false)
    (hx : boolWordToNat (wireValues (List.range' 4 256) s) < 2 ^ 256 - (2 ^ 32 + 977)) :
    let after := modularDoubleIdealState (List.range' 4 256) secp256k1ReductionConstantBits
      (2 ^ 256 - (2 ^ 32 + 977)) 0 s
    boolWordToNat (wireValues (List.range' 4 256) after) =
      (2 * boolWordToNat (wireValues (List.range' 4 256) s)) % (2 ^ 256 - (2 ^ 32 + 977)) ∧
    (∀ w, w ∉ List.range' 4 256 → after w = s w) ∧
    (∀ branch ∈ secp256k1ModularDouble.run, branch.history.length = 511 ∧
      branch.kraus (Quantum.ket s) = Quantum.registerXResetMagnitude 511 • Quantum.ket after) ∧
    Quantum.Instrument.bornMass secp256k1ModularDouble.run (Quantum.ket s) = 1 ∧
    secp256k1ModularDouble.WellFormed ∧
    gidneyToffoliCount secp256k1ModularDouble = 1531 ∧
    gidneyCnotCount secp256k1ModularDouble = 3649 ∧
    secp256k1ModularDouble.tCount = 10717 ∧
    secp256k1ModularDouble.measurementCount = 511 ∧
    secp256k1ModularDouble.qubitCount = 516 := by
  have hd : (4 :: List.range' 5 255).length = (List.range' 260 256).length := by simp
  have hk : (4 :: List.range' 5 255).length = secp256k1ReductionConstantBits.length := by simp [secp256k1ReductionConstantBits]
  have hp : 2 ^ 256 - (2 ^ 32 + 977) < 2 ^ (4 :: List.range' 5 255).length := by decide
  have hodd : (2 ^ 256 - (2 ^ 32 + 977)) % 2 = 1 := by decide
  have hv : boolWordToNat secp256k1ReductionConstantBits =
      2 ^ (4 :: List.range' 5 255).length - (2 ^ 256 - (2 ^ 32 + 977)) := by
    rw [secp256k1ReductionConstant_value]; decide
  have hl := (doubling_layout (List.range' 4 256) (List.range' 260 256) 1 2 3 0 doublingProduction_layout).1
  have hw := modularDouble_wellFormed 4 (List.range' 5 255) (List.range' 260 256) _
    (2 ^ 256 - (2 ^ 32 + 977)) 1 2 3 0 hk hd doublingProduction_layout
  have ha := modularDoubleIdealState_correct 4 0 (List.range' 5 255) _ _ s hl hf hk hp hx hodd hv
  dsimp only
  refine ⟨ha.1,ha.2,?_,?_,hw,doublingProduction_counts.1,doublingProduction_counts.2.1,
    doublingProduction_counts.2.2.1,doublingProduction_counts.2.2.2,doublingProduction_qubits⟩
  · intro branch hb
    have h := modularDouble_branch_correct 4 (List.range' 5 255) (List.range' 260 256) _ _
      1 2 3 0 s hk hd doublingProduction_layout hc hr ht hf hp hx hodd hv branch hb
    have hz : secp256k1ReductionConstantBits.all (fun k => !k) = false := by decide
    simpa only [List.length_range',List.length_cons,List.length_take,hz,Bool.false_eq_true,↓reduceIte] using h
  · exact Quantum.AdaptiveCircuit.run_bornMass_eq_one _ hw _ (Quantum.normSq_ket s)

end ShorECDLP.Paper2607_13816
