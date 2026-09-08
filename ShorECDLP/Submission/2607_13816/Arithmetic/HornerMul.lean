import ShorECDLP.Submission.«2607_13816».Arithmetic.Doubling

/-!
# Quadratic Horner multiplication

Controls are little-endian, so recursion visits their tail before their head.
The most significant bit adds into the initially zero output; every remaining
bit doubles and then conditionally adds. The source reuses the addend as dirty
workspace and exchanges the carry/flag roles in each doubling call.
-/
namespace ShorECDLP.Paper2607_13816
open Classical
set_option linter.unusedSimpArgs false

/-- The literal MSB-first doubling/addition schedule from the pinned source. -/
def hornerMul (controls input acc : List Wire) (correction : List Bool) (p : Nat)
    (c r t f : Wire) : Quantum.AdaptiveCircuit :=
  match controls with
  | [] => .done
  | q :: qs => (hornerMul qs input acc correction p c r t f).seq
      (if qs = [] then controlledModularAdd input acc correction p q c r t f else
        (modularDouble acc input correction p f r t c).seq
          (controlledModularAdd input acc correction p q c r t f))

/-- The composed ideal state, retaining the same reusable physical registers. -/
def hornerMulIdealState (controls input acc : List Wire) (correction : List Bool) (p : Nat)
    (c f : Wire) (s : BasisState) : BasisState :=
  match controls with
  | [] => s
  | q :: qs =>
      let before := hornerMulIdealState qs input acc correction p c f s
      let ready := if qs = [] then before else modularDoubleIdealState acc correction p c before
      modularAddIdealState input acc correction p q c f ready

private theorem horner_base_layout (controls input acc : List Wire) (c r t f : Wire)
    (hnd : ([c,r,t,f] ++ controls ++ input ++ acc).Nodup) :
    ([c,r,t,f] ++ input ++ acc).Nodup := by
  have hs := (List.sublist_append_right controls (input ++ acc)).append_left [c,r,t,f]
  apply List.Nodup.sublist hs
  all_goals simpa only [List.append_assoc] using hnd

private theorem horner_tail_layout (q : Wire) (qs input acc : List Wire) (c r t f : Wire)
    (hnd : ([c,r,t,f] ++ (q :: qs) ++ input ++ acc).Nodup) :
    ([c,r,t,f] ++ qs ++ input ++ acc).Nodup := by
  have hs := ((List.Sublist.cons q (List.Sublist.refl qs)).append_right input).append_right acc
  exact List.Nodup.sublist (hs.append_left [c,r,t,f]) (by simpa only [List.append_assoc] using hnd)

private theorem horner_add_layout (q : Wire) (qs input acc : List Wire) (c r t f : Wire)
    (hnd : ([c,r,t,f] ++ (q :: qs) ++ input ++ acc).Nodup) :
    ([q,c,r,t,f] ++ input ++ acc).Nodup := by
  have hp : ([q,c,r,t,f] ++ qs ++ input ++ acc).Perm
      ([c,r,t,f] ++ (q :: qs) ++ input ++ acc) := by
    have h := (List.perm_append_comm (l₁ := [q]) (l₂ := [c,r,t,f])).append_right qs
    simpa only [List.append_assoc] using (h.append_right input).append_right acc
  have hn := hp.nodup_iff.mpr hnd
  have hs := (List.sublist_append_right qs (input ++ acc)).append_left [q,c,r,t,f]
  exact List.Nodup.sublist hs (by simpa only [List.append_assoc] using hn)

theorem horner_double_layout (controls input acc : List Wire) (c r t f : Wire)
    (hnd : ([c,r,t,f] ++ controls ++ input ++ acc).Nodup) :
    ([f,r,t,c] ++ acc ++ input).Nodup := by
  have hn := horner_base_layout controls input acc c r t f hnd
  have hp : ([f,r,t,c] : List Wire).Perm [c,r,t,f] :=
    (List.perm_append_comm (l₁ := [f,r,t]) (l₂ := [c])).trans
      ((List.perm_append_comm (l₁ := [f]) (l₂ := [r,t])).cons c)
  have hq := (hp.append_right acc).append_right input
  apply hq.nodup_iff.mpr
  have hs := (List.perm_append_comm (l₁ := acc) (l₂ := input)).append_left [c,r,t,f]
  exact hs.nodup_iff.mpr (by simpa only [List.append_assoc] using hn)

/-- Each iteration is well formed under one persistent shared layout. -/
theorem hornerMul_wellFormed (controls input : List Wire) (a : Wire) (rest : List Wire)
    (correction : List Bool) (p : Nat) (c r t f : Wire)
    (hlen : input.length = (a :: rest).length) (hk : (a :: rest).length = correction.length)
    (hnd : ([c,r,t,f] ++ controls ++ input ++ (a :: rest)).Nodup) :
    (hornerMul controls input (a :: rest) correction p c r t f).WellFormed := by
  induction controls with
  | nil => trivial
  | cons q qs ih =>
    apply Quantum.AdaptiveCircuit.WellFormed.seq
    · exact ih (horner_tail_layout q qs input (a :: rest) c r t f hnd)
    · have ha := controlledModularAdd_wellFormed input (a :: rest) correction p q c r t f hlen
        (by simp) hk (horner_add_layout q qs input (a :: rest) c r t f hnd)
      by_cases hqs : qs = []
      · simpa only [if_pos hqs] using ha
      · simp only [if_neg hqs]
        exact Quantum.AdaptiveCircuit.WellFormed.seq
          (modularDouble_wellFormed a rest input correction p f r t c hk hlen.symm
            (horner_double_layout (q :: qs) input (a :: rest) c r t f hnd)) ha

private theorem horner_geometry (controls input acc : List Wire) (c r t f : Wire)
    (hnd : ([c,r,t,f] ++ controls ++ input ++ acc).Nodup) :
    ∀ w ∈ [c,r,t,f] ++ controls ++ input, w ∉ acc := by
  intro w hw ha
  exact (List.nodup_append.mp hnd).2.2 w hw w ha rfl

theorem horner_frame_word (acc ws : List Wire) (before after : BasisState)
    (hf : ∀ w, w ∉ acc → after w = before w) (hw : ∀ w ∈ ws, w ∉ acc) :
    wireValues ws after = wireValues ws before := by
  apply List.map_congr_left
  exact fun w h => hf w (hw w h)

theorem horner_numeric_step (p x y : Nat) (b : Bool) :
    (((2 * (y*x % p)) % p) + if b then y else 0) % p = (y * (b.toNat + 2*x)) % p := by
  cases b <;> simp only [Bool.toNat, Bool.cond_false, Bool.cond_true, Bool.false_eq_true,
    ↓reduceIte, Nat.zero_add, Nat.add_zero, Nat.mod_mod, Nat.mul_mod_mod, Nat.mul_add,
    Nat.mul_one, Nat.mul_zero]
  · congr 1; ring
  · rw [Nat.mod_add_mod]
    congr 1; ring


/-- Starting from a zero output, the ideal schedule computes the product modulo
`p` and preserves the multiplier, addend and all auxiliary wires. -/
theorem hornerMulIdealState_correct (controls input : List Wire) (a : Wire) (rest : List Wire)
    (correction : List Bool) (p : Nat) (c r t f : Wire) (s : BasisState)
    (hlen : input.length = (a :: rest).length) (hk : (a :: rest).length = correction.length)
    (hnd : ([c,r,t,f] ++ controls ++ input ++ (a :: rest)).Nodup)
    (hc : s c = false) (hf : s f = false)
    (hp : p < 2 ^ (a :: rest).length) (hodd : p % 2 = 1)
    (hx : boolWordToNat (wireValues input s) < p)
    (hzero : boolWordToNat (wireValues (a :: rest) s) = 0)
    (hconstant : boolWordToNat correction = 2 ^ (a :: rest).length - p) :
    boolWordToNat (wireValues (a :: rest) (hornerMulIdealState controls input (a :: rest) correction p c f s)) =
      (boolWordToNat (wireValues input s) * boolWordToNat (wireValues controls s)) % p ∧
    ∀ w, w ∉ a :: rest → hornerMulIdealState controls input (a :: rest) correction p c f s w = s w := by
  have hp0 : 0 < p := by omega
  induction controls with
  | nil =>
    constructor
    · simpa [hornerMulIdealState,wireValues,boolWordToNat] using hzero
    · intro w hw; rfl
  | cons q qs ih =>
    have htail := horner_tail_layout q qs input (a :: rest) c r t f hnd
    have hi := ih htail
    have hg := horner_geometry (q :: qs) input (a :: rest) c r t f hnd
    have hq : q ∉ a :: rest := hg q (by simp)
    have hin : ∀ w ∈ input, w ∉ a :: rest := fun w hw => hg w (by simp [hw])
    have haLayout := horner_add_layout q qs input (a :: rest) c r t f hnd
    by_cases hqs : qs = []
    · subst qs
      have ha := modularAddIdealState_correct input (a :: rest) correction p q c r t f s hlen hk
        haLayout hc hf hp hx (by omega) hconstant
      change boolWordToNat (wireValues (a :: rest) (modularAddIdealState input (a :: rest) correction p q c f s)) = _ ∧ _
      refine ⟨?_,ha.2⟩
      rw [ha.1,hzero]
      cases hb : s q <;> simp [wireValues,boolWordToNat,hb]
    · let before := hornerMulIdealState qs input (a :: rest) correction p c f s
      have hbval : boolWordToNat (wireValues (a :: rest) before) =
          (boolWordToNat (wireValues input s) * boolWordToNat (wireValues qs s)) % p := hi.1
      have hbframe : ∀ w, w ∉ a :: rest → before w = s w := hi.2
      have hbc : before c = false := (hbframe c (hg c (by simp))).trans hc
      have hcanonical : boolWordToNat (wireValues (a :: rest) before) < p := by rw [hbval]; exact Nat.mod_lt _ hp0
      have hdLayout := horner_double_layout (q :: qs) input (a :: rest) c r t f hnd
      have hshiftLayout : (c :: a :: rest).Nodup := by
        have hbase := (List.nodup_append.mp hdLayout).1
        have hdis := (List.nodup_append.mp hbase).2
        exact List.nodup_cons.mpr ⟨fun hw => hdis.2 c (by simp) c hw rfl,hdis.1⟩
      have hd := modularDoubleIdealState_correct a c rest correction p before hshiftLayout hbc hk hp hcanonical hodd hconstant
      let ready := modularDoubleIdealState (a :: rest) correction p c before
      have hrframe : ∀ w, w ∉ a :: rest → ready w = s w := fun w hw => (hd.2 w hw).trans (hbframe w hw)
      have hrinput := horner_frame_word (a :: rest) input s ready hrframe hin
      have hrq : ready q = s q := hrframe q hq
      have hrvalue : boolWordToNat (wireValues (a :: rest) ready) =
          (2 * ((boolWordToNat (wireValues input s) * boolWordToNat (wireValues qs s)) % p)) % p := by
        exact hd.1.trans (by rw [hbval])
      have ha := modularAddIdealState_correct input (a :: rest) correction p q c r t f ready hlen hk
        haLayout ((hrframe c (hg c (by simp))).trans hc) ((hrframe f (hg f (by simp))).trans hf) hp
        (by rw [hrinput]; exact hx) (by rw [hrvalue]; exact Nat.mod_lt _ hp0) hconstant
      have heq : hornerMulIdealState (q :: qs) input (a :: rest) correction p c f s =
          modularAddIdealState input (a :: rest) correction p q c f ready := by
        simp only [hornerMulIdealState,if_neg hqs]
        rfl
      rw [heq]
      refine ⟨?_,fun w hw => (ha.2 w hw).trans (hrframe w hw)⟩
      rw [ha.1,hrinput,hrq,hrvalue]
      exact horner_numeric_step p (boolWordToNat (wireValues qs s)) (boolWordToNat (wireValues input s)) (s q)

theorem horner_seq_branch (g h : Quantum.AdaptiveCircuit) (s mid out : BasisState)
    (hg : ∀ b ∈ g.run, b.kraus (Quantum.ket s) =
      Quantum.registerXResetMagnitude b.history.length • Quantum.ket mid)
    (hh : ∀ b ∈ h.run, b.kraus (Quantum.ket mid) =
      Quantum.registerXResetMagnitude b.history.length • Quantum.ket out)
    (b : Quantum.InstrumentBranch) (hb : b ∈ (g.seq h).run) :
    b.kraus (Quantum.ket s) = Quantum.registerXResetMagnitude b.history.length • Quantum.ket out := by
  simp only [Quantum.AdaptiveCircuit.run_seq,Quantum.Instrument.seq,List.mem_flatMap,List.mem_map] at hb
  obtain ⟨b₁,h₁,b₂,h₂,rfl⟩ := hb
  simp only [Quantum.InstrumentBranch.seq,LinearMap.comp_apply,List.length_append]
  rw [hg b₁ h₁,map_smul,hh b₂ h₂]
  simp only [smul_smul,Quantum.registerXResetMagnitude,← pow_add]

/-- Every measurement branch realizes the same modular product state, with
positive amplitude determined solely by its measurement history. -/
theorem hornerMul_branch_correct (controls input : List Wire) (a : Wire) (rest : List Wire)
    (correction : List Bool) (p : Nat) (c r t f : Wire) (s : BasisState)
    (hlen : input.length = (a :: rest).length) (hk : (a :: rest).length = correction.length)
    (hnd : ([c,r,t,f] ++ controls ++ input ++ (a :: rest)).Nodup)
    (hc : s c = false) (hr : s r = false) (ht : s t = false) (hf : s f = false)
    (hp : p < 2 ^ (a :: rest).length) (hodd : p % 2 = 1)
    (hx : boolWordToNat (wireValues input s) < p)
    (hzero : boolWordToNat (wireValues (a :: rest) s) = 0)
    (hconstant : boolWordToNat correction = 2 ^ (a :: rest).length - p)
    (branch : Quantum.InstrumentBranch)
    (hb : branch ∈ (hornerMul controls input (a :: rest) correction p c r t f).run) :
    branch.kraus (Quantum.ket s) = Quantum.registerXResetMagnitude branch.history.length •
      Quantum.ket (hornerMulIdealState controls input (a :: rest) correction p c f s) := by
  have hp0 : 0 < p := by omega
  induction controls generalizing branch with
  | nil =>
    have hd := gidneyDoneBranch branch hb
    rw [hd.2,hd.1]
    simp [Quantum.registerXResetMagnitude,hornerMulIdealState]
  | cons q qs ih =>
    have htail := horner_tail_layout q qs input (a :: rest) c r t f hnd
    have hi := hornerMulIdealState_correct qs input a rest correction p c r t f s hlen hk htail
      hc hf hp hodd hx hzero hconstant
    have hg := horner_geometry (q :: qs) input (a :: rest) c r t f hnd
    let before := hornerMulIdealState qs input (a :: rest) correction p c f s
    have hbframe : ∀ w, w ∉ a :: rest → before w = s w := hi.2
    have hbinput := horner_frame_word (a :: rest) input s before hbframe (fun w hw => hg w (by simp [hw]))
    have hbclean : ∀ w ∈ [c,r,t,f], before w = s w := fun w hw => hbframe w (hg w (by simp only [List.mem_append]; exact Or.inl (Or.inl hw)))
    have hbcanon : boolWordToNat (wireValues (a :: rest) before) < p := by rw [hi.1]; exact Nat.mod_lt _ hp0
    have haLayout := horner_add_layout q qs input (a :: rest) c r t f hnd
    apply horner_seq_branch _ _ s before _ (fun b hb => ih htail b hb) _ branch hb
    by_cases hqs : qs = []
    · simp only [if_pos hqs]
      intro b hmem
      have ha := controlledModularAdd_branch_correct input (a :: rest) correction p q c r t f before
        hlen (by simp) hk haLayout ((hbclean c (by simp)).trans hc) ((hbclean r (by simp)).trans hr)
        ((hbclean t (by simp)).trans ht) ((hbclean f (by simp)).trans hf) hp
        (by rw [hbinput]; exact hx) hbcanon hconstant b hmem
      rw [ha.1]
      simpa only [hornerMulIdealState,if_pos hqs] using ha.2
    · simp only [if_neg hqs]
      have hdLayout := horner_double_layout (q :: qs) input (a :: rest) c r t f hnd
      have hshiftLayout : (c :: a :: rest).Nodup := by
        have hbase := (List.nodup_append.mp hdLayout).1
        have hdis := (List.nodup_append.mp hbase).2
        exact List.nodup_cons.mpr ⟨fun hw => hdis.2 c (by simp) c hw rfl,hdis.1⟩
      let ready := modularDoubleIdealState (a :: rest) correction p c before
      have hd := modularDoubleIdealState_correct a c rest correction p before hshiftLayout
        ((hbclean c (by simp)).trans hc) hk hp hbcanon hodd hconstant
      have hrframe : ∀ w, w ∉ a :: rest → ready w = s w := fun w hw => (hd.2 w hw).trans (hbframe w hw)
      have hrclean : ∀ w ∈ [c,r,t,f], ready w = s w := fun w hw => hrframe w (hg w (by simp only [List.mem_append]; exact Or.inl (Or.inl hw)))
      have hrinput := horner_frame_word (a :: rest) input s ready hrframe (fun w hw => hg w (by simp [hw]))
      intro b hmem
      apply horner_seq_branch _ _ before ready _ _ _ b hmem
      · intro db hdb
        have dh := modularDouble_branch_correct a rest input correction p f r t c before hk hlen.symm hdLayout
          ((hbclean f (by simp)).trans hf) ((hbclean r (by simp)).trans hr)
          ((hbclean t (by simp)).trans ht) ((hbclean c (by simp)).trans hc) hp hbcanon hodd hconstant db hdb
        rw [dh.1]; exact dh.2
      · intro ab hab
        have ah := controlledModularAdd_branch_correct input (a :: rest) correction p q c r t f ready
          hlen (by simp) hk haLayout ((hrclean c (by simp)).trans hc) ((hrclean r (by simp)).trans hr)
          ((hrclean t (by simp)).trans ht) ((hrclean f (by simp)).trans hf) hp
          (by rw [hrinput]; exact hx) (by rw [hd.1]; exact Nat.mod_lt _ hp0) hconstant ab hab
        rw [ah.1]
        simpa only [hornerMulIdealState,if_neg hqs] using ah.2

set_option maxRecDepth 100000 in
private theorem hornerAdd_decompose (q c r t f : Wire) : controlledModularAdd (List.range' 260 256) (List.range' 4 256)
    secp256k1ReductionConstantBits (2 ^ 256 - (2 ^ 32 + 977)) q c r t f =
    .unitary (controlledAddCarry (List.range' 260 256) (List.range' 4 256) q c f)
      ((gidneyCompareGE (List.range' 4 256) (List.range' 260 256) (2 ^ 256 - (2 ^ 32 + 977)) c r t f).seq
        ((controlledGidneyAddConst (List.range' 4 256) (List.range' 260 255) secp256k1ReductionConstantBits f c r t).seq
          (.unitary (controlledCompareLT (List.range' 4 256) (List.range' 260 256) q c f) .done))) := by
  unfold controlledModularAdd
  rw [show (List.range' 4 256).length - 1 = 255 from rfl,
    show (List.range' 260 256).take 255 = List.range' 260 255 from rfl]

set_option maxRecDepth 100000 in
theorem hornerAdd_counts (q c r t f : Wire) :
    let g := controlledModularAdd (List.range' 260 256) (List.range' 4 256)
      secp256k1ReductionConstantBits (2 ^ 256 - (2 ^ 32 + 977)) q c r t f
    gidneyToffoliCount g = 2813 ∧ gidneyCnotCount g = 4929 ∧ g.tCount = 19691 ∧ g.measurementCount = 511 := by
  have ha := secp256k1GidneyAdd_counts f c r t
  have hg := secp256k1ModularCompare_counts c r t f
  have hl := controlledCompareLT_counts 4 (List.range' 5 255) (List.range' 260 256) q c f (by simp)
  change eeaToffoliCount (controlledCompareLT (List.range' 4 256) (List.range' 260 256) q c f) = 513 ∧
    eeaCnotCount (controlledCompareLT (List.range' 4 256) (List.range' 260 256) q c f) = 1024 ∧
    eeaXCount (controlledCompareLT (List.range' 4 256) (List.range' 260 256) q c f) = 516 ∧
    tCount (controlledCompareLT (List.range' 4 256) (List.range' 260 256) q c f) = 3591 at hl
  have ht := controlledAddCarry_toffoliCount (List.range' 260 256) (List.range' 4 256) q c f (by simp)
  have hc := controlledAddCarry_cnotCount (List.range' 260 256) (List.range' 4 256) q c f (by simp)
  have hT := controlledAddCarry_tCount (List.range' 260 256) (List.range' 4 256) q c f (by simp)
  dsimp only
  rw [hornerAdd_decompose]
  have hfour := doublingFour_counts (controlledAddCarry (List.range' 260 256) (List.range' 4 256) q c f)
    (controlledCompareLT (List.range' 4 256) (List.range' 260 256) q c f)
    (gidneyCompareGE (List.range' 4 256) (List.range' 260 256) (2 ^ 256 - (2 ^ 32 + 977)) c r t f)
    (controlledGidneyAddConst (List.range' 4 256) (List.range' 260 255) secp256k1ReductionConstantBits f c r t)
  exact ⟨hfour.1.trans (by rw [ht,hg.1,ha.1,hl.1]; rfl),
    hfour.2.1.trans (by rw [hc,hg.2.1,ha.2.1,hl.2.1]; rfl),
    hfour.2.2.1.trans (by rw [hT,hg.2.2.1,ha.2.2.1,hl.2.2.2]; rfl),
    hfour.2.2.2.trans (by rw [hg.2.2.2,ha.2.2.2])⟩

set_option maxRecDepth 100000 in
private theorem hornerDouble_decompose (c r t f : Wire) : modularDouble (List.range' 4 256) (List.range' 260 256)
    secp256k1ReductionConstantBits (2 ^ 256 - (2 ^ 32 + 977)) c r t f =
    .unitary (doublingShift (List.range' 4 256) f)
      ((gidneyCompareGE (List.range' 4 256) (List.range' 260 256) (2 ^ 256 - (2 ^ 32 + 977)) c r t f).seq
        ((controlledGidneyAddConst (List.range' 4 256) (List.range' 260 255) secp256k1ReductionConstantBits f c r t).seq
          (.unitary [.CX 4 f] .done))) := by
  rw [show List.range' 4 256 = 4 :: List.range' 5 255 from rfl]
  unfold modularDouble
  dsimp only
  rw [show (List.range' 260 256).take (List.range' 5 255).length = List.range' 260 255 from rfl]

set_option maxRecDepth 100000 in
theorem hornerDouble_counts (c r t f : Wire) :
    let g := modularDouble (List.range' 4 256) (List.range' 260 256)
      secp256k1ReductionConstantBits (2 ^ 256 - (2 ^ 32 + 977)) c r t f
    gidneyToffoliCount g = 1531 ∧ gidneyCnotCount g = 3649 ∧ g.tCount = 10717 ∧ g.measurementCount = 511 := by
  have ha := secp256k1GidneyAdd_counts f c r t
  have hg := secp256k1ModularCompare_counts c r t f
  have hs := doublingShift_counts 4 f (List.range' 5 255)
  change eeaToffoliCount (doublingShift (List.range' 4 256) f) = 0 ∧
    eeaCnotCount (doublingShift (List.range' 4 256) f) = 767 ∧
    tCount (doublingShift (List.range' 4 256) f) = 0 at hs
  dsimp only
  rw [hornerDouble_decompose]
  have hfour := doublingFour_counts (doublingShift (List.range' 4 256) f) ([.CX 4 f] : Circuit)
    (gidneyCompareGE (List.range' 4 256) (List.range' 260 256) (2 ^ 256 - (2 ^ 32 + 977)) c r t f)
    (controlledGidneyAddConst (List.range' 4 256) (List.range' 260 255) secp256k1ReductionConstantBits f c r t)
  exact ⟨hfour.1.trans (by rw [hs.1,hg.1,ha.1]; rfl),
    hfour.2.1.trans (by rw [hs.2.1,hg.2.1,ha.2.1]; rfl),
    hfour.2.2.1.trans (by rw [hs.2.2,hg.2.2.1,ha.2.2.1]; rfl),
    hfour.2.2.2.trans (by rw [hg.2.2.2,ha.2.2.2])⟩

private theorem horner_counts (controls : List Wire) (c r t f : Wire) :
    let g := hornerMul controls (List.range' 260 256) (List.range' 4 256)
      secp256k1ReductionConstantBits (2 ^ 256 - (2 ^ 32 + 977)) c r t f
    gidneyToffoliCount g = controls.length * 2813 + (controls.length - 1) * 1531 ∧
    gidneyCnotCount g = controls.length * 4929 + (controls.length - 1) * 3649 ∧
    g.tCount = controls.length * 19691 + (controls.length - 1) * 10717 ∧
    g.measurementCount = (controls.length * 2 - 1) * 511 := by
  have hseqT (a b : Quantum.AdaptiveCircuit) : (a.seq b).tCount = a.tCount + b.tCount := by
    simpa only [gidneyGateCount_tCount] using modularGateCount_seq tCost a b
  have hseqCCX (a b : Quantum.AdaptiveCircuit) : gidneyToffoliCount (a.seq b) =
      gidneyToffoliCount a + gidneyToffoliCount b := modularGateCount_seq _ a b
  have hseqCX (a b : Quantum.AdaptiveCircuit) : gidneyCnotCount (a.seq b) =
      gidneyCnotCount a + gidneyCnotCount b := modularGateCount_seq _ a b
  induction controls with
  | nil => simp [hornerMul,gidneyToffoliCount,gidneyCnotCount,gidneyGateCount,
      Quantum.AdaptiveCircuit.tCount,Quantum.AdaptiveCircuit.measurementCount]
  | cons q qs ih =>
    have ha := hornerAdd_counts q c r t f
    have hd := hornerDouble_counts f r t c
    dsimp only at ih ha hd ⊢
    rw [hornerMul]
    by_cases hz : qs = []
    · rw [if_pos hz]
      simp only [hseqCCX,hseqCX,hseqT,modularMeasurements_seq,ih.1,ih.2.1,ih.2.2.1,ih.2.2.2,
        ha.1,ha.2.1,ha.2.2.1,ha.2.2.2]
      subst qs; simp
    · rw [if_neg hz]
      simp only [hseqCCX,hseqCX,hseqT,modularMeasurements_seq,ih.1,ih.2.1,ih.2.2.1,ih.2.2.2,
        ha.1,ha.2.1,ha.2.2.1,ha.2.2.2,hd.1,hd.2.1,hd.2.2.1,hd.2.2.2,List.length_cons]
      have hn : qs.length ≠ 0 := fun h => hz (List.eq_nil_of_length_eq_zero h)
      omega

private theorem hornerConstantAdd_wires (q c r t w : Wire) :
    w ∈ (controlledGidneyAddConst (List.range' 4 256) (List.range' 260 255)
      secp256k1ReductionConstantBits q c r t).wires ↔
      w ∈ [q,c,r,t] ++ List.range' 4 256 ++ List.range' 260 255 := by
  exact controlledGidneyAddConst_wires 4 260 q c r t (List.range' 5 255) (List.range' 261 254)
    ((List.range' 1 255).map (Nat.testBit (2 ^ 32 + 977))) (by simp) (by simp) w

set_option maxRecDepth 100000 in
theorem hornerAdd_wires (q c r t f w : Wire) :
    w ∈ (controlledModularAdd (List.range' 260 256) (List.range' 4 256)
      secp256k1ReductionConstantBits (2 ^ 256 - (2 ^ 32 + 977)) q c r t f).wires ↔
      w ∈ [q,c,r,t,f] ++ List.range' 4 256 ++ List.range' 260 256 := by
  rw [hornerAdd_decompose]
  simp only [Quantum.AdaptiveCircuit.wires,List.mem_append,modularWires_seq,
    hornerConstantAdd_wires,List.not_mem_nil,or_false]
  rw [secp256k1ModularCompare_wires c r t f w]
  have hl : w ∈ circuitWires (controlledCompareLT (List.range' 4 256) (List.range' 260 256) q c f) ↔
      w ∈ [q,c,f] ++ List.range' 4 256 ++ List.range' 260 256 :=
    controlledCompareLT_wires 4 (List.range' 5 255) (List.range' 260 256) q c f w (by simp)
  rw [hl]
  have hfirst : w ∈ circuitWires (controlledAddCarry (List.range' 260 256) (List.range' 4 256) q c f) →
      w ∈ [q,c,f] ++ List.range' 260 256 ++ List.range' 4 256 := by
    intro hw
    obtain ⟨g,hg,hw⟩ := List.mem_flatMap.mp hw
    exact controlledAddCarry_usesOnly (List.range' 260 256) (List.range' 4 256) q c f g hg w hw
  simp at hfirst ⊢
  dsimp only [Wire] at *
  by_cases hmem : w ∈ circuitWires (controlledAddCarry (List.range' 260 256) (List.range' 4 256) q c f)
  · have hh := hfirst hmem; simp only [hmem,true_or,true_iff]; omega
  · simp only [hmem,false_or]; omega

set_option maxRecDepth 100000 in
theorem hornerDouble_wires (c r t f w : Wire) :
    w ∈ (modularDouble (List.range' 4 256) (List.range' 260 256)
      secp256k1ReductionConstantBits (2 ^ 256 - (2 ^ 32 + 977)) c r t f).wires ↔
      w ∈ [c,r,t,f] ++ List.range' 4 256 ++ List.range' 260 256 := by
  rw [hornerDouble_decompose]
  simp only [Quantum.AdaptiveCircuit.wires,List.mem_append,modularWires_seq,
    hornerConstantAdd_wires,List.not_mem_nil,or_false]
  rw [secp256k1ModularCompare_wires c r t f w]
  have hfirst : w ∈ circuitWires (doublingShift (List.range' 4 256) f) →
      w ∈ f :: List.range' 4 256 := by
    intro hw
    obtain ⟨g,hg,hw⟩ := List.mem_flatMap.mp hw
    exact doublingShift_usesOnly 4 f (List.range' 5 255) g hg w hw
  have hlast : w ∈ circuitWires [.CX 4 f] ↔ w = 4 ∨ w = f := by simp [circuitWires,gateWires]
  rw [hlast]
  simp at hfirst ⊢
  dsimp only [Wire] at *
  by_cases hmem : w ∈ circuitWires (doublingShift (List.range' 4 256) f)
  · have hh := hfirst hmem; simp only [hmem,true_or,true_iff]; omega
  · simp only [hmem,false_or]; omega

private theorem horner_wires (controls : List Wire) (c r t f w : Wire) :
    w ∈ (hornerMul controls (List.range' 260 256) (List.range' 4 256)
      secp256k1ReductionConstantBits (2 ^ 256 - (2 ^ 32 + 977)) c r t f).wires ↔
      w ∈ controls ∨ (controls ≠ [] ∧ w ∈ [c,r,t,f] ++ List.range' 4 256 ++ List.range' 260 256) := by
  induction controls with
  | nil => simp [hornerMul,Quantum.AdaptiveCircuit.wires]
  | cons q qs ih =>
    rw [hornerMul,modularWires_seq,ih]
    by_cases hz : qs = []
    · rw [if_pos hz,hornerAdd_wires]
      subst qs
      simp only [List.mem_cons,List.not_mem_nil,List.mem_append,or_false,ne_eq,not_true_eq_false,false_and,
        List.cons_ne_self,List.cons_ne_nil,not_false_eq_true,true_and]
      tauto
    · rw [if_neg hz,modularWires_seq,hornerDouble_wires,hornerAdd_wires]
      simp only [hz,not_false_eq_true,true_and,List.mem_cons,List.mem_append,List.not_mem_nil,or_false,
        List.cons_ne_nil,ne_eq]
      tauto

-- Keep the fixed certificate symbolic instead of unfolding its measurement tree.
attribute [local irreducible] hornerMul hornerMulIdealState

/-- Production multiplication: two 256-bit inputs, a zero 256-bit output, and
four clean scalar wires. The addend is borrowed during each doubling. -/
def secp256k1HornerMul : Quantum.AdaptiveCircuit :=
  hornerMul (List.range' 516 256) (List.range' 260 256) (List.range' 4 256)
    secp256k1ReductionConstantBits (2 ^ 256 - (2 ^ 32 + 977)) 1 2 3 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem hornerProduction_layout :
    ([1,2,3,0] ++ List.range' 516 256 ++ List.range' 260 256 ++ (4 :: List.range' 5 255)).Nodup := by
  change ([1,2,3,0] ++ List.range' 516 256 ++ List.range' 260 256 ++ List.range' 4 256 : List Nat).Nodup
  simp only [List.nodup_append]
  refine ⟨⟨⟨by decide,List.nodup_range',?_⟩,List.nodup_range',?_⟩,List.nodup_range',?_⟩
  all_goals
    intro a ha b hb he
    simp at ha hb
    omega


set_option maxRecDepth 100000 in
private theorem hornerProduction_qubits : secp256k1HornerMul.qubitCount = 772 := by
  have heq : secp256k1HornerMul.wires.dedup.toFinset = (List.range' 0 772).toFinset := by
    ext w
    simp only [List.mem_toFinset,List.mem_dedup,secp256k1HornerMul,horner_wires]
    have hn : List.range' 516 256 ≠ [] := by decide
    simp [hn]
    dsimp only [Wire] at *
    omega
  have hc := congrArg Finset.card heq
  simpa only [List.toFinset_card_of_nodup (List.nodup_dedup _),
    List.toFinset_card_of_nodup (List.nodup_range'),List.length_range'] using hc

set_option maxRecDepth 100000 in
set_option maxHeartbeats 200000 in
/-- Readable same-circuit certificate: modular multiplication, complete frame
restoration, normalized quantum branches, and exact gate/reset/wire resources.
The multiplier may be any 256-bit word; the borrowed addend is canonical. -/
theorem secp256k1HornerMul_correct_resources (s : BasisState)
    (hc : s 1 = false) (hr : s 2 = false) (ht : s 3 = false) (hf : s 0 = false)
    (hx : boolWordToNat (wireValues (List.range' 260 256) s) < 2 ^ 256 - (2 ^ 32 + 977))
    (hzero : boolWordToNat (wireValues (List.range' 4 256) s) = 0) :
    let after := hornerMulIdealState (List.range' 516 256) (List.range' 260 256) (List.range' 4 256)
      secp256k1ReductionConstantBits (2 ^ 256 - (2 ^ 32 + 977)) 1 0 s
    boolWordToNat (wireValues (List.range' 4 256) after) =
      (boolWordToNat (wireValues (List.range' 260 256) s) *
        boolWordToNat (wireValues (List.range' 516 256) s)) % (2 ^ 256 - (2 ^ 32 + 977)) ∧
    (∀ w, w ∉ List.range' 4 256 → after w = s w) ∧
    (∀ branch ∈ secp256k1HornerMul.run, branch.kraus (Quantum.ket s) =
      Quantum.registerXResetMagnitude branch.history.length • Quantum.ket after) ∧
    Quantum.Instrument.bornMass secp256k1HornerMul.run (Quantum.ket s) = 1 ∧
    secp256k1HornerMul.WellFormed ∧
    gidneyToffoliCount secp256k1HornerMul = 1110533 ∧
    gidneyCnotCount secp256k1HornerMul = 2192319 ∧
    secp256k1HornerMul.tCount = 7773731 ∧
    secp256k1HornerMul.measurementCount = 261121 ∧
    secp256k1HornerMul.qubitCount = 772 := by
  have hlen : (List.range' 260 256).length = (4 :: List.range' 5 255).length := by simp
  have hk : (4 :: List.range' 5 255).length = secp256k1ReductionConstantBits.length := by simp [secp256k1ReductionConstantBits]
  have hp : 2 ^ 256 - (2 ^ 32 + 977) < 2 ^ (4 :: List.range' 5 255).length := by decide
  have hodd : (2 ^ 256 - (2 ^ 32 + 977)) % 2 = 1 := by decide
  have hv : boolWordToNat secp256k1ReductionConstantBits =
      2 ^ (4 :: List.range' 5 255).length - (2 ^ 256 - (2 ^ 32 + 977)) := by
    rw [secp256k1ReductionConstant_value]; decide
  have hw : (hornerMul (List.range' 516 256) (List.range' 260 256) (4 :: List.range' 5 255)
      secp256k1ReductionConstantBits (2 ^ 256 - (2 ^ 32 + 977)) 1 2 3 0).WellFormed :=
    hornerMul_wellFormed (List.range' 516 256) (List.range' 260 256) 4 (List.range' 5 255)
    secp256k1ReductionConstantBits (2 ^ 256 - (2 ^ 32 + 977)) 1 2 3 0 hlen hk hornerProduction_layout
  have ha := hornerMulIdealState_correct (List.range' 516 256) (List.range' 260 256) 4 (List.range' 5 255)
    secp256k1ReductionConstantBits (2 ^ 256 - (2 ^ 32 + 977)) 1 2 3 0 s hlen hk hornerProduction_layout
    hc hf hp hodd hx hzero hv
  have hn := horner_counts (List.range' 516 256) 1 2 3 0
  dsimp only
  refine ⟨ha.1,ha.2,?_,?_,hw,hn.1,hn.2.1,hn.2.2.1,hn.2.2.2,hornerProduction_qubits⟩
  · intro branch hb
    exact hornerMul_branch_correct (List.range' 516 256) (List.range' 260 256) 4 (List.range' 5 255)
      secp256k1ReductionConstantBits (2 ^ 256 - (2 ^ 32 + 977)) 1 2 3 0 s hlen hk hornerProduction_layout
      hc hr ht hf hp hodd hx hzero hv branch hb
  · exact Quantum.AdaptiveCircuit.run_bornMass_eq_one _ hw _ (Quantum.normSq_ket s)

end ShorECDLP.Paper2607_13816
