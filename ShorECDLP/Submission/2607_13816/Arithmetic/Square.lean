import ShorECDLP.Submission.«2607_13816».Arithmetic.HornerMul

/-!
# Quadratic squaring

Each input bit is copied to a clean control before modular addition and un-copied
when the borrowed input has been restored. This follows the pinned source while
allowing the multiplicand to supply its own multiplier bits.
-/
namespace ShorECDLP.Paper2607_13816
open Classical
set_option linter.unusedSimpArgs false

/-- Copy the current input bit, perform modular addition, and un-copy it. -/
def squareAdd (input acc : List Wire) (correction : List Bool) (p : Nat)
    (q copied c r t f : Wire) : Quantum.AdaptiveCircuit :=
  .unitary [.CX q copied] ((controlledModularAdd input acc correction p copied c r t f).seq
    (.unitary [.CX q copied] .done))

/-- The exact ideal state of the copied-control addition. -/
def squareAddIdealState (input acc : List Wire) (correction : List Bool) (p : Nat)
    (q copied c f : Wire) (s : BasisState) : BasisState :=
  run [.CX q copied] (modularAddIdealState input acc correction p copied c f (run [.CX q copied] s))

private theorem square_geometry (input acc : List Wire) (copied c r t f : Wire)
    (hnd : ([copied,c,r,t,f] ++ input ++ acc).Nodup) :
    (∀ w ∈ [copied,c,r,t,f] ++ input, w ∉ acc) ∧
    (∀ w ∈ c :: r :: t :: f :: input, w ≠ copied) := by
  constructor
  · intro w hw ha
    exact (List.nodup_append.mp hnd).2.2 w hw w ha rfl
  · have hn := (List.nodup_append.mp hnd).1
    have hc : copied ∉ c :: r :: t :: f :: input := (List.nodup_cons.mp hn).1
    intro w hw he; subst w; exact hc hw

private theorem square_word_copy (ws : List Wire) (q copied : Wire) (s : BasisState)
    (h : copied ∉ ws) : wireValues ws (run [.CX q copied] s) = wireValues ws s := by
  apply List.map_congr_left
  intro w hw
  have hn : w ≠ copied := fun he => h (he ▸ hw)
  simp [run,applyGate,upd,hn]

/-- The copied bit is cleared after the addend is restored, including when that
bit is one. All wires outside the accumulator retain their initial values. -/
theorem squareAddIdealState_correct (input acc : List Wire) (correction : List Bool) (p : Nat)
    (q copied c r t f : Wire) (s : BasisState)
    (hlen : input.length = acc.length) (hk : acc.length = correction.length)
    (hnd : ([copied,c,r,t,f] ++ input ++ acc).Nodup) (hq : q ∈ input)
    (hcopy : s copied = false) (hc : s c = false) (hf : s f = false)
    (hp : p < 2 ^ acc.length) (hx : boolWordToNat (wireValues input s) < p)
    (hy : boolWordToNat (wireValues acc s) < p)
    (hconstant : boolWordToNat correction = 2 ^ acc.length - p) :
    boolWordToNat (wireValues acc (squareAddIdealState input acc correction p q copied c f s)) =
      (boolWordToNat (wireValues acc s) + if s q then boolWordToNat (wireValues input s) else 0) % p ∧
    ∀ w, w ∉ acc → squareAddIdealState input acc correction p q copied c f s w = s w := by
  have hg := square_geometry input acc copied c r t f hnd
  have hca : copied ∉ acc := hg.1 copied (by simp)
  have hci : copied ∉ input := fun h => hg.2 copied (by simp [h]) rfl
  have hqa : q ∉ acc := hg.1 q (by simp [hq])
  have hqc : q ≠ copied := hg.2 q (by simp [hq])
  let before := run [.CX q copied] s
  have hbword := square_word_copy acc q copied s hca
  have hbinput := square_word_copy input q copied s hci
  have hbclean (w : Wire) (hw : w ∈ [c,r,t,f]) : before w = s w := by
    have hn : w ≠ copied := hg.2 w (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hw ⊢; tauto)
    simp [before,run,applyGate,upd,hn]
  have ha := modularAddIdealState_correct input acc correction p copied c r t f before hlen hk hnd
    ((hbclean c (by simp)).trans hc) ((hbclean f (by simp)).trans hf) hp
    (by rw [hbinput]; exact hx) (by rw [hbword]; exact hy) hconstant
  let mid := modularAddIdealState input acc correction p copied c f before
  have hmidcopy : mid copied = s q := by
    exact (ha.2 copied hca).trans (by simp [before,run,applyGate,upd,hcopy])
  have hmidq : mid q = s q := by
    exact (ha.2 q hqa).trans (by simp [before,run,applyGate,upd,hqc])
  constructor
  · change boolWordToNat (wireValues acc (run [.CX q copied] mid)) = _
    rw [square_word_copy acc q copied mid hca,ha.1,hbword,hbinput]
    simp [before,run,applyGate,upd,hcopy]
  · intro w hw
    change run [.CX q copied] mid w = s w
    by_cases he : w = copied
    · subst w
      simp [run,applyGate,upd,hmidcopy,hmidq,hcopy]
    · have hm : mid w = before w := ha.2 w hw
      calc
        run [.CX q copied] mid w = mid w := by simp [run,applyGate,upd,he]
        _ = before w := hm
        _ = s w := by simp [before,run,applyGate,upd,he]

/-- Copy/un-copy gates are well formed even though the selected bit belongs to
 the word borrowed by the enclosed modular adder. -/
theorem squareAdd_wellFormed (input acc : List Wire) (correction : List Bool) (p : Nat)
    (q copied c r t f : Wire) (hlen : input.length = acc.length) (hne : 0 < acc.length)
    (hk : acc.length = correction.length) (hnd : ([copied,c,r,t,f] ++ input ++ acc).Nodup)
    (hq : q ∈ input) : (squareAdd input acc correction p q copied c r t f).WellFormed := by
  have hqc : q ≠ copied := (square_geometry input acc copied c r t f hnd).2 q (by simp [hq])
  have hg : CircuitWellFormed [.CX q copied] := by simp [CircuitWellFormed,Gate.WellFormed,hqc]
  exact ⟨hg,Quantum.AdaptiveCircuit.WellFormed.seq
    (controlledModularAdd_wellFormed input acc correction p copied c r t f hlen hne hk hnd) ⟨hg,True.intro⟩⟩

/-- Copying and un-copying introduce no measurement or phase; the enclosed
modular addition supplies the same input-independent branch amplitude. -/
theorem squareAdd_branch_correct (input acc : List Wire) (correction : List Bool) (p : Nat)
    (q copied c r t f : Wire) (s : BasisState)
    (hlen : input.length = acc.length) (hne : 0 < acc.length) (hk : acc.length = correction.length)
    (hnd : ([copied,c,r,t,f] ++ input ++ acc).Nodup)
    (hc : s c = false) (hr : s r = false) (ht : s t = false) (hf : s f = false)
    (hp : p < 2 ^ acc.length) (hx : boolWordToNat (wireValues input s) < p)
    (hy : boolWordToNat (wireValues acc s) < p)
    (hconstant : boolWordToNat correction = 2 ^ acc.length - p)
    (branch : Quantum.InstrumentBranch) (hb : branch ∈ (squareAdd input acc correction p q copied c r t f).run) :
    let m := acc.length + if correction.all (fun k => !k) then 0 else (input.take (acc.length-1)).length
    branch.history.length = m ∧ branch.kraus (Quantum.ket s) = Quantum.registerXResetMagnitude m •
      Quantum.ket (squareAddIdealState input acc correction p q copied c f s) := by
  have hg := square_geometry input acc copied c r t f hnd
  have hca : copied ∉ acc := hg.1 copied (by simp)
  have hci : copied ∉ input := fun h => hg.2 copied (by simp [h]) rfl
  let before := run [.CX q copied] s
  have hbclean (w : Wire) (hw : w ∈ [c,r,t,f]) : before w = s w := by
    have hn : w ≠ copied := hg.2 w (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hw ⊢; tauto)
    simp [before,run,applyGate,upd,hn]
  obtain ⟨after,ha,hh,hbranch⟩ := gidneyUnitaryBranch [.CX q copied] _ branch hb
  simp only [Quantum.AdaptiveCircuit.run_seq,Quantum.Instrument.seq,List.mem_flatMap,List.mem_map,
    Quantum.AdaptiveCircuit.run_unitary_done,List.mem_singleton] at ha
  obtain ⟨addBranch,haddBranch,last,rfl,rfl⟩ := ha
  have hadd := controlledModularAdd_branch_correct input acc correction p copied c r t f before hlen hne hk hnd
    ((hbclean c (by simp)).trans hc) ((hbclean r (by simp)).trans hr)
    ((hbclean t (by simp)).trans ht) ((hbclean f (by simp)).trans hf) hp
    (by rw [square_word_copy input q copied s hci]; exact hx)
    (by rw [square_word_copy acc q copied s hca]; exact hy) hconstant addBranch haddBranch
  dsimp only at hadd ⊢
  constructor
  · rw [hh]
    simpa only [Quantum.InstrumentBranch.seq,List.length_append,List.length_nil,Nat.add_zero] using hadd.1
  · rw [hbranch]
    simp only [Quantum.InstrumentBranch.seq,LinearMap.comp_apply]
    rw [Quantum.run_ket_agrees_classical _ _ (by simp),hadd.2,map_smul,
      Quantum.run_ket_agrees_classical _ _ (by simp)]
    rfl

/-- Literal MSB-first squaring loop. The selected bits may belong to the borrowed
input because each addition copies its control into a separate clean wire. -/
def squareLoop (controls input acc : List Wire) (correction : List Bool) (p : Nat)
    (copied c r t f : Wire) : Quantum.AdaptiveCircuit :=
  match controls with
  | [] => .done
  | q :: qs => (squareLoop qs input acc correction p copied c r t f).seq
      (if qs = [] then squareAdd input acc correction p q copied c r t f else
        (modularDouble acc input correction p f r t c).seq
          (squareAdd input acc correction p q copied c r t f))

def squareLoopIdealState (controls input acc : List Wire) (correction : List Bool) (p : Nat)
    (copied c f : Wire) (s : BasisState) : BasisState :=
  match controls with
  | [] => s
  | q :: qs =>
      let before := squareLoopIdealState qs input acc correction p copied c f s
      let ready := if qs = [] then before else modularDoubleIdealState acc correction p c before
      squareAddIdealState input acc correction p q copied c f ready

private theorem square_double_layout (input acc : List Wire) (copied c r t f : Wire)
    (hnd : ([copied,c,r,t,f] ++ input ++ acc).Nodup) :
    ([f,r,t,c] ++ acc ++ input).Nodup := by
  have hbase : ([c,r,t,f] ++ [] ++ input ++ acc).Nodup := (List.nodup_cons.mp hnd).2
  exact horner_double_layout [] input acc c r t f hbase

/-- The source loop preserves one shared layout through every iteration. -/
theorem squareLoop_wellFormed (controls input : List Wire) (a : Wire) (rest : List Wire)
    (correction : List Bool) (p : Nat) (copied c r t f : Wire)
    (hlen : input.length = (a :: rest).length) (hk : (a :: rest).length = correction.length)
    (hnd : ([copied,c,r,t,f] ++ input ++ (a :: rest)).Nodup)
    (hcontrols : ∀ q ∈ controls, q ∈ input) :
    (squareLoop controls input (a :: rest) correction p copied c r t f).WellFormed := by
  induction controls with
  | nil => trivial
  | cons q qs ih =>
    apply Quantum.AdaptiveCircuit.WellFormed.seq
    · exact ih (fun w hw => hcontrols w (List.mem_cons_of_mem q hw))
    · have ha := squareAdd_wellFormed input (a :: rest) correction p q copied c r t f hlen
        (by simp) hk hnd (hcontrols q (by simp))
      by_cases hz : qs = []
      · simpa only [if_pos hz] using ha
      · simp only [if_neg hz]
        exact Quantum.AdaptiveCircuit.WellFormed.seq
          (modularDouble_wellFormed a rest input correction p f r t c hk hlen.symm
            (square_double_layout input (a :: rest) copied c r t f hnd)) ha

/-- Numeric Horner induction with controls selected from the borrowed input.
The copied bit and every wire outside the output are restored. -/
theorem squareLoopIdealState_correct (controls input : List Wire) (a : Wire) (rest : List Wire)
    (correction : List Bool) (p : Nat) (copied c r t f : Wire) (s : BasisState)
    (hlen : input.length = (a :: rest).length) (hk : (a :: rest).length = correction.length)
    (hnd : ([copied,c,r,t,f] ++ input ++ (a :: rest)).Nodup)
    (hcontrols : ∀ q ∈ controls, q ∈ input)
    (hcopy : s copied = false) (hc : s c = false) (hf : s f = false)
    (hp : p < 2 ^ (a :: rest).length) (hodd : p % 2 = 1)
    (hx : boolWordToNat (wireValues input s) < p)
    (hzero : boolWordToNat (wireValues (a :: rest) s) = 0)
    (hconstant : boolWordToNat correction = 2 ^ (a :: rest).length - p) :
    boolWordToNat (wireValues (a :: rest) (squareLoopIdealState controls input (a :: rest) correction p copied c f s)) =
      (boolWordToNat (wireValues input s) * boolWordToNat (wireValues controls s)) % p ∧
    ∀ w, w ∉ a :: rest → squareLoopIdealState controls input (a :: rest) correction p copied c f s w = s w := by
  have hp0 : 0 < p := by omega
  induction controls with
  | nil =>
    constructor
    · simpa [squareLoopIdealState,wireValues,boolWordToNat] using hzero
    · intro w hw; rfl
  | cons q qs ih =>
    have hq := hcontrols q (by simp)
    have hi := ih (fun w hw => hcontrols w (List.mem_cons_of_mem q hw))
    have hg := (square_geometry input (a :: rest) copied c r t f hnd).1
    have hin : ∀ w ∈ input, w ∉ a :: rest := fun w hw => hg w (by simp [hw])
    by_cases hz : qs = []
    · subst qs
      have ha := squareAddIdealState_correct input (a :: rest) correction p q copied c r t f s
        hlen hk hnd hq hcopy hc hf hp hx (by omega) hconstant
      change boolWordToNat (wireValues (a :: rest) (squareAddIdealState input (a :: rest) correction p q copied c f s)) = _ ∧ _
      refine ⟨?_,ha.2⟩
      rw [ha.1,hzero]
      cases hb : s q <;> simp [wireValues,boolWordToNat,hb]
    · let before := squareLoopIdealState qs input (a :: rest) correction p copied c f s
      have hbval : boolWordToNat (wireValues (a :: rest) before) =
          (boolWordToNat (wireValues input s) * boolWordToNat (wireValues qs s)) % p := hi.1
      have hbframe : ∀ w, w ∉ a :: rest → before w = s w := hi.2
      have hcanonical : boolWordToNat (wireValues (a :: rest) before) < p := by rw [hbval]; exact Nat.mod_lt _ hp0
      have hshift : (c :: a :: rest).Nodup := List.nodup_cons.mpr
        ⟨hg c (by simp),(List.nodup_append.mp hnd).2.1⟩
      have hd := modularDoubleIdealState_correct a c rest correction p before hshift
        ((hbframe c (hg c (by simp))).trans hc) hk hp hcanonical hodd hconstant
      let ready := modularDoubleIdealState (a :: rest) correction p c before
      have hrframe : ∀ w, w ∉ a :: rest → ready w = s w := fun w hw => (hd.2 w hw).trans (hbframe w hw)
      have hrinput := horner_frame_word (a :: rest) input s ready hrframe hin
      have hrq : ready q = s q := hrframe q (hin q hq)
      have hrval : boolWordToNat (wireValues (a :: rest) ready) =
          (2 * ((boolWordToNat (wireValues input s) * boolWordToNat (wireValues qs s)) % p)) % p :=
        hd.1.trans (by rw [hbval])
      have ha := squareAddIdealState_correct input (a :: rest) correction p q copied c r t f ready hlen hk hnd hq
        ((hrframe copied (hg copied (by simp))).trans hcopy) ((hrframe c (hg c (by simp))).trans hc)
        ((hrframe f (hg f (by simp))).trans hf) hp (by rw [hrinput]; exact hx)
        (by rw [hrval]; exact Nat.mod_lt _ hp0) hconstant
      have heq : squareLoopIdealState (q :: qs) input (a :: rest) correction p copied c f s =
          squareAddIdealState input (a :: rest) correction p q copied c f ready := by
        simp only [squareLoopIdealState,if_neg hz]; rfl
      rw [heq]
      refine ⟨?_,fun w hw => (ha.2 w hw).trans (hrframe w hw)⟩
      rw [ha.1,hrinput,hrq,hrval]
      exact horner_numeric_step p (boolWordToNat (wireValues qs s)) (boolWordToNat (wireValues input s)) (s q)

/-- Every squaring-loop branch implements the same ideal state with positive
input-independent amplitude. -/
theorem squareLoop_branch_correct (controls input : List Wire) (a : Wire) (rest : List Wire)
    (correction : List Bool) (p : Nat) (copied c r t f : Wire) (s : BasisState)
    (hlen : input.length = (a :: rest).length) (hk : (a :: rest).length = correction.length)
    (hnd : ([copied,c,r,t,f] ++ input ++ (a :: rest)).Nodup)
    (hcontrols : ∀ q ∈ controls, q ∈ input)
    (hcopy : s copied = false)
    (hc : s c = false) (hr : s r = false) (ht : s t = false) (hf : s f = false)
    (hp : p < 2 ^ (a :: rest).length) (hodd : p % 2 = 1)
    (hx : boolWordToNat (wireValues input s) < p)
    (hzero : boolWordToNat (wireValues (a :: rest) s) = 0)
    (hconstant : boolWordToNat correction = 2 ^ (a :: rest).length - p)
    (branch : Quantum.InstrumentBranch)
    (hb : branch ∈ (squareLoop controls input (a :: rest) correction p copied c r t f).run) :
    branch.kraus (Quantum.ket s) = Quantum.registerXResetMagnitude branch.history.length •
      Quantum.ket (squareLoopIdealState controls input (a :: rest) correction p copied c f s) := by
  have hp0 : 0 < p := by omega
  induction controls generalizing branch with
  | nil =>
    have hd := gidneyDoneBranch branch hb
    rw [hd.2,hd.1]
    simp [Quantum.registerXResetMagnitude,squareLoopIdealState]
  | cons q qs ih =>
    have htail : ∀ w ∈ qs, w ∈ input := fun w hw => hcontrols w (List.mem_cons_of_mem q hw)
    have hi := squareLoopIdealState_correct qs input a rest correction p copied c r t f s hlen hk hnd htail
      hcopy hc hf hp hodd hx hzero hconstant
    have hg := (square_geometry input (a :: rest) copied c r t f hnd).1
    let before := squareLoopIdealState qs input (a :: rest) correction p copied c f s
    have hbframe : ∀ w, w ∉ a :: rest → before w = s w := hi.2
    have hbinput := horner_frame_word (a :: rest) input s before hbframe (fun w hw => hg w (by simp [hw]))
    have hbclean : ∀ w ∈ [c,r,t,f], before w = s w := fun w hw => hbframe w (hg w (by simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw ⊢; tauto))
    have hbcanon : boolWordToNat (wireValues (a :: rest) before) < p := by rw [hi.1]; exact Nat.mod_lt _ hp0
    apply horner_seq_branch _ _ s before _ (fun b hb => ih htail b hb) _ branch hb
    by_cases hqs : qs = []
    · simp only [if_pos hqs]
      intro b hmem
      have ha := squareAdd_branch_correct input (a :: rest) correction p q copied c r t f before
        hlen (by simp) hk hnd ((hbclean c (by simp)).trans hc) ((hbclean r (by simp)).trans hr)
        ((hbclean t (by simp)).trans ht) ((hbclean f (by simp)).trans hf) hp
        (by rw [hbinput]; exact hx) hbcanon hconstant b hmem
      rw [ha.1]
      simpa only [squareLoopIdealState,if_pos hqs] using ha.2
    · simp only [if_neg hqs]
      have hdLayout := square_double_layout input (a :: rest) copied c r t f hnd
      have hshiftLayout : (c :: a :: rest).Nodup := by
        have hbase := (List.nodup_append.mp hdLayout).1
        have hdis := (List.nodup_append.mp hbase).2
        exact List.nodup_cons.mpr ⟨fun hw => hdis.2 c (by simp) c hw rfl,hdis.1⟩
      let ready := modularDoubleIdealState (a :: rest) correction p c before
      have hd := modularDoubleIdealState_correct a c rest correction p before hshiftLayout
        ((hbclean c (by simp)).trans hc) hk hp hbcanon hodd hconstant
      have hrframe : ∀ w, w ∉ a :: rest → ready w = s w := fun w hw => (hd.2 w hw).trans (hbframe w hw)
      have hrclean : ∀ w ∈ [c,r,t,f], ready w = s w := fun w hw => hrframe w (hg w (by simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw ⊢; tauto))
      have hrinput := horner_frame_word (a :: rest) input s ready hrframe (fun w hw => hg w (by simp [hw]))
      intro b hmem
      apply horner_seq_branch _ _ before ready _ _ _ b hmem
      · intro db hdb
        have dh := modularDouble_branch_correct a rest input correction p f r t c before hk hlen.symm hdLayout
          ((hbclean f (by simp)).trans hf) ((hbclean r (by simp)).trans hr)
          ((hbclean t (by simp)).trans ht) ((hbclean c (by simp)).trans hc) hp hbcanon hodd hconstant db hdb
        rw [dh.1]; exact dh.2
      · intro ab hab
        have ah := squareAdd_branch_correct input (a :: rest) correction p q copied c r t f ready
          hlen (by simp) hk hnd ((hrclean c (by simp)).trans hc) ((hrclean r (by simp)).trans hr)
          ((hrclean t (by simp)).trans ht) ((hrclean f (by simp)).trans hf) hp
          (by rw [hrinput]; exact hx) (by rw [hd.1]; exact Nat.mod_lt _ hp0) hconstant ab hab
        rw [ah.1]
        simpa only [squareLoopIdealState,if_neg hqs] using ah.2

private theorem squareWrap_counts (g h : Circuit) (a : Quantum.AdaptiveCircuit) :
    gidneyToffoliCount (.unitary g (a.seq (.unitary h .done))) =
      eeaToffoliCount g + (gidneyToffoliCount a + eeaToffoliCount h) ∧
    gidneyCnotCount (.unitary g (a.seq (.unitary h .done))) =
      eeaCnotCount g + (gidneyCnotCount a + eeaCnotCount h) ∧
    (Quantum.AdaptiveCircuit.unitary g (a.seq (.unitary h .done))).tCount =
      tCount g + (a.tCount + tCount h) ∧
    (Quantum.AdaptiveCircuit.unitary g (a.seq (.unitary h .done))).measurementCount = a.measurementCount := by
  have hfour := doublingFour_counts g h a .done
  simpa only [Quantum.AdaptiveCircuit.seq,gidneyToffoliCount,gidneyCnotCount,gidneyGateCount,
    Quantum.AdaptiveCircuit.tCount,Quantum.AdaptiveCircuit.measurementCount,Nat.zero_add,Nat.add_zero] using hfour

private theorem squareAdd_counts (q copied c r t f : Wire) :
    let g := squareAdd (List.range' 260 256) (List.range' 4 256)
      secp256k1ReductionConstantBits (2 ^ 256 - (2 ^ 32 + 977)) q copied c r t f
    gidneyToffoliCount g = 2813 ∧ gidneyCnotCount g = 4931 ∧ g.tCount = 19691 ∧ g.measurementCount = 511 := by
  have ha := hornerAdd_counts copied c r t f
  have hw := squareWrap_counts ([.CX q copied] : Circuit) ([.CX q copied] : Circuit)
    (controlledModularAdd (List.range' 260 256) (List.range' 4 256)
      secp256k1ReductionConstantBits (2 ^ 256 - (2 ^ 32 + 977)) copied c r t f)
  dsimp only
  exact ⟨hw.1.trans (by rw [ha.1]; rfl),hw.2.1.trans (by rw [ha.2.1]; rfl),
    hw.2.2.1.trans (by rw [ha.2.2.1]; rfl),hw.2.2.2.trans ha.2.2.2⟩

private theorem square_counts (controls : List Wire) (copied c r t f : Wire) :
    let g := squareLoop controls (List.range' 260 256) (List.range' 4 256)
      secp256k1ReductionConstantBits (2 ^ 256 - (2 ^ 32 + 977)) copied c r t f
    gidneyToffoliCount g = controls.length * 2813 + (controls.length - 1) * 1531 ∧
    gidneyCnotCount g = controls.length * 4931 + (controls.length - 1) * 3649 ∧
    g.tCount = controls.length * 19691 + (controls.length - 1) * 10717 ∧
    g.measurementCount = (controls.length * 2 - 1) * 511 := by
  have hseqT (a b : Quantum.AdaptiveCircuit) : (a.seq b).tCount = a.tCount + b.tCount := by
    simpa only [gidneyGateCount_tCount] using modularGateCount_seq tCost a b
  have hseqCCX (a b : Quantum.AdaptiveCircuit) : gidneyToffoliCount (a.seq b) =
      gidneyToffoliCount a + gidneyToffoliCount b := modularGateCount_seq _ a b
  have hseqCX (a b : Quantum.AdaptiveCircuit) : gidneyCnotCount (a.seq b) =
      gidneyCnotCount a + gidneyCnotCount b := modularGateCount_seq _ a b
  induction controls with
  | nil => simp [squareLoop,gidneyToffoliCount,gidneyCnotCount,gidneyGateCount,
      Quantum.AdaptiveCircuit.tCount,Quantum.AdaptiveCircuit.measurementCount]
  | cons q qs ih =>
    have ha := squareAdd_counts q copied c r t f
    have hd := hornerDouble_counts f r t c
    dsimp only at ih ha hd ⊢
    rw [squareLoop]
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

private theorem squareAdd_wires (q copied c r t f w : Wire) :
    w ∈ (squareAdd (List.range' 260 256) (List.range' 4 256)
      secp256k1ReductionConstantBits (2 ^ 256 - (2 ^ 32 + 977)) q copied c r t f).wires ↔
      w ∈ [q,copied,c,r,t,f] ++ List.range' 4 256 ++ List.range' 260 256 := by
  unfold squareAdd
  simp only [Quantum.AdaptiveCircuit.wires,modularWires_seq,List.mem_append,
    List.not_mem_nil,or_false]
  rw [hornerAdd_wires copied c r t f w]
  simp [circuitWires,gateWires]
  tauto

private theorem square_wires (controls : List Wire) (copied c r t f w : Wire) :
    w ∈ (squareLoop controls (List.range' 260 256) (List.range' 4 256)
      secp256k1ReductionConstantBits (2 ^ 256 - (2 ^ 32 + 977)) copied c r t f).wires ↔
      w ∈ controls ∨ (controls ≠ [] ∧ w ∈ [copied,c,r,t,f] ++ List.range' 4 256 ++ List.range' 260 256) := by
  induction controls with
  | nil => simp [squareLoop,Quantum.AdaptiveCircuit.wires]
  | cons q qs ih =>
    rw [squareLoop,modularWires_seq,ih]
    by_cases hz : qs = []
    · rw [if_pos hz,squareAdd_wires]
      subst qs
      simp only [List.mem_cons,List.not_mem_nil,List.mem_append,or_false,ne_eq,not_true_eq_false,false_and,
        List.cons_ne_self,List.cons_ne_nil,not_false_eq_true,true_and]
      tauto
    · rw [if_neg hz,modularWires_seq,hornerDouble_wires,squareAdd_wires]
      simp only [hz,not_false_eq_true,true_and,List.mem_cons,List.mem_append,List.not_mem_nil,or_false,
        List.cons_ne_nil,ne_eq]
      tauto

-- The fixed certificate uses the proved loop lemmas without expanding the tree.
attribute [local irreducible] squareLoop squareLoopIdealState

/-- Concrete production squaring with one copied control and four arithmetic
auxiliaries, all initially clean. The input is borrowed and restored. -/
def secp256k1Square : Quantum.AdaptiveCircuit :=
  squareLoop (List.range' 260 256) (List.range' 260 256) (List.range' 4 256)
    secp256k1ReductionConstantBits (2 ^ 256 - (2 ^ 32 + 977)) 516 1 2 3 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem squareProduction_layout :
    ([516,1,2,3,0] ++ List.range' 260 256 ++ (4 :: List.range' 5 255)).Nodup := by decide

set_option maxRecDepth 100000 in
private theorem squareProduction_qubits : secp256k1Square.qubitCount = 517 := by
  have heq : secp256k1Square.wires.dedup.toFinset = (List.range' 0 517).toFinset := by
    ext w
    simp only [List.mem_toFinset,List.mem_dedup,secp256k1Square,square_wires]
    have hn : List.range' 260 256 ≠ [] := by decide
    simp [hn]
    dsimp only [Wire] at *
    omega
  have hc := congrArg Finset.card heq
  simpa only [List.toFinset_card_of_nodup (List.nodup_dedup _),
    List.toFinset_card_of_nodup (List.nodup_range'),List.length_range'] using hc

set_option maxRecDepth 100000 in
/-- Readable same-circuit certificate for squaring: canonical square modulo the
prime, complete frame restoration, normalized quantum branches and exact resources. -/
theorem secp256k1Square_correct_resources (s : BasisState)
    (hcopy : s 516 = false) (hc : s 1 = false) (hr : s 2 = false) (ht : s 3 = false) (hf : s 0 = false)
    (hx : boolWordToNat (wireValues (List.range' 260 256) s) < 2 ^ 256 - (2 ^ 32 + 977))
    (hzero : boolWordToNat (wireValues (List.range' 4 256) s) = 0) :
    let after := squareLoopIdealState (List.range' 260 256) (List.range' 260 256) (List.range' 4 256)
      secp256k1ReductionConstantBits (2 ^ 256 - (2 ^ 32 + 977)) 516 1 0 s
    boolWordToNat (wireValues (List.range' 4 256) after) =
      (boolWordToNat (wireValues (List.range' 260 256) s)) ^ 2 % (2 ^ 256 - (2 ^ 32 + 977)) ∧
    (∀ w, w ∉ List.range' 4 256 → after w = s w) ∧
    (∀ branch ∈ secp256k1Square.run, branch.kraus (Quantum.ket s) =
      Quantum.registerXResetMagnitude branch.history.length • Quantum.ket after) ∧
    Quantum.Instrument.bornMass secp256k1Square.run (Quantum.ket s) = 1 ∧
    secp256k1Square.WellFormed ∧
    gidneyToffoliCount secp256k1Square = 1110533 ∧
    gidneyCnotCount secp256k1Square = 2192831 ∧
    secp256k1Square.tCount = 7773731 ∧
    secp256k1Square.measurementCount = 261121 ∧
    secp256k1Square.qubitCount = 517 := by
  have hlen : (List.range' 260 256).length = (4 :: List.range' 5 255).length := by simp
  have hk : (4 :: List.range' 5 255).length = secp256k1ReductionConstantBits.length := by simp [secp256k1ReductionConstantBits]
  have hp : 2 ^ 256 - (2 ^ 32 + 977) < 2 ^ (4 :: List.range' 5 255).length := by decide
  have hodd : (2 ^ 256 - (2 ^ 32 + 977)) % 2 = 1 := by decide
  have hv : boolWordToNat secp256k1ReductionConstantBits =
      2 ^ (4 :: List.range' 5 255).length - (2 ^ 256 - (2 ^ 32 + 977)) := by
    rw [secp256k1ReductionConstant_value]; decide
  have hcontrols : ∀ q ∈ List.range' 260 256, q ∈ List.range' 260 256 := fun _ h => h
  have hw : (squareLoop (List.range' 260 256) (List.range' 260 256) (4 :: List.range' 5 255)
      secp256k1ReductionConstantBits (2 ^ 256 - (2 ^ 32 + 977)) 516 1 2 3 0).WellFormed :=
    squareLoop_wellFormed (List.range' 260 256) (List.range' 260 256) 4 (List.range' 5 255)
      secp256k1ReductionConstantBits (2 ^ 256 - (2 ^ 32 + 977)) 516 1 2 3 0 hlen hk squareProduction_layout hcontrols
  have ha := squareLoopIdealState_correct (List.range' 260 256) (List.range' 260 256) 4 (List.range' 5 255)
    secp256k1ReductionConstantBits (2 ^ 256 - (2 ^ 32 + 977)) 516 1 2 3 0 s hlen hk squareProduction_layout hcontrols
    hcopy hc hf hp hodd hx hzero hv
  have hn := square_counts (List.range' 260 256) 516 1 2 3 0
  dsimp only
  refine ⟨?_,ha.2,?_,?_,hw,hn.1,hn.2.1,hn.2.2.1,hn.2.2.2,squareProduction_qubits⟩
  · simpa only [pow_two] using ha.1
  · intro branch hb
    exact squareLoop_branch_correct (List.range' 260 256) (List.range' 260 256) 4 (List.range' 5 255)
      secp256k1ReductionConstantBits (2 ^ 256 - (2 ^ 32 + 977)) 516 1 2 3 0 s hlen hk squareProduction_layout hcontrols
      hcopy hc hr ht hf hp hodd hx hzero hv branch hb
  · exact Quantum.AdaptiveCircuit.run_bornMass_eq_one _ hw _ (Quantum.normSq_ket s)

end ShorECDLP.Paper2607_13816
