import ShorECDLP.Submission.«2607_13816».EEA.EpochCompression
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
attribute [local irreducible] canonicalWork2Rotation terminalEpochCompression secp256k1EEAForwardUnitary eeaPreprocessIdealState
noncomputable section
/-- Source postprocessing: complement Iter, conditionally subtract the coefficient from the modulus, then restore Iter. -/
def eeaParityCorrection (input dirty : List Wire) (modulus : List Bool)
    (c r t iter : Wire) : AdaptiveCircuit :=
  .unitary [.X iter] ((controlledConstMinus input dirty modulus iter c r t).seq
    (.unitary [.X iter] .done))
private def eeaParityCorrectionIdealState (input : List Wire) (modulus : List Bool)
    (iter : Wire) (s : BasisState) : BasisState :=
  let after := constMinusIdealState input modulus iter (s[iter ↦ !s iter])
  after[iter ↦ !after iter]
private theorem eeaParityCorrectionIdealState_correct (input : List Wire) (modulus : List Bool)
    (p iter : Nat) (s : BasisState) (hn : 0 < input.length) (hk : input.length=modulus.length)
    (hnd : input.Nodup) (hi : iter∉input) (hp : p<2^input.length)
    (hm : boolWordToNat modulus=p) (hx : boolWordToNat (wireValues input s)≤p) :
    let out := eeaParityCorrectionIdealState input modulus iter s
    boolWordToNat (wireValues input out)=
      (if s iter then boolWordToNat (wireValues input s) else p-boolWordToNat (wireValues input s)) ∧
    ∀ w∉input,out w=s w := by
  let flipped := s[iter ↦ !s iter]
  have hinput : wireValues input flipped=wireValues input s := by
    apply List.map_congr_left
    intro w hw
    exact upd_other _ _ _ (by intro h; subst w; exact hi hw)
  have hc := constMinusIdealState_correct input modulus iter p flipped hn hk hnd hi hp hm (by rw [hinput];exact hx)
  let after := constMinusIdealState input modulus iter flipped
  have hafter : after iter= !s iter := by simpa only [flipped,upd_same] using hc.2 iter hi
  have hout : wireValues input (eeaParityCorrectionIdealState input modulus iter s)=wireValues input after := by
    apply List.map_congr_left
    intro w hw
    exact upd_other _ _ _ (by intro h; subst w; exact hi hw)
  constructor
  · rw [hout,hc.1,hinput]
    rw [show flipped iter= !s iter from by simp [flipped]]
    cases s iter <;> rfl
  · intro w hw
    change (after[iter ↦ !after iter]) w=s w
    by_cases hwi : w=iter
    · subst w; simp [upd,hafter]
    · rw [upd_other _ _ _ hwi]
      exact (hc.2 w hw).trans (upd_other _ _ _ hwi)
private theorem eeaParityCorrection_branch_correct (input dirty : List Wire) (modulus : List Bool)
    (c r t iter : Wire) (s : BasisState)
    (hk : input.length=modulus.length) (hd : input.length=dirty.length+1)
    (hnd : ([iter,c,r,t]++input++dirty).Nodup)
    (hc : s c=false) (hr : s r=false) (ht : s t=false)
    (branch : InstrumentBranch) (hb : branch∈(eeaParityCorrection input dirty modulus c r t iter).run) :
    branch.kraus (ket s)=registerXResetMagnitude branch.history.length •
      ket (eeaParityCorrectionIdealState input modulus iter s) := by
  have hm := (List.nodup_append.mp (List.nodup_append.mp hnd).1).1
  have hci : c≠iter := by simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or] at hm; tauto
  have hri : r≠iter := by simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or] at hm; tauto
  have hti : t≠iter := by simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or] at hm; tauto
  obtain ⟨rest,hh,hist,hkraus⟩ := gidneyUnitaryBranch _ _ branch hb
  rw [hkraus,Quantum.run_ket_agrees_classical _ _ (by simp [HPFree]),hist]
  let flipped := s[iter ↦ !s iter]
  apply horner_seq_branch _ _ flipped (constMinusIdealState input modulus iter flipped)
    (eeaParityCorrectionIdealState input modulus iter s) _ _ rest hh
  · intro b hb
    exact controlledConstMinus_branch_correct input dirty modulus iter c r t flipped hk hd hnd
      (by simp [flipped,upd,hci,hc]) (by simp [flipped,upd,hri,hr]) (by simp [flipped,upd,hti,ht]) b hb
  · intro b hb
    obtain ⟨last,hl,hh,hk⟩ := gidneyUnitaryBranch _ _ b hb
    have hd := gidneyDoneBranch last hl
    rw [hk,hd.2,Quantum.run_ket_agrees_classical _ _ (by simp [HPFree]),hh,hd.1]
    simp only [List.length_nil,registerXResetMagnitude,pow_zero,one_smul]
    rfl
/-- The parity-correction circuit on the production coefficient and borrowed workspace. -/
def secp256k1EEAParityCorrection : AdaptiveCircuit :=
  eeaParityCorrection (List.range' 263 256) (List.range' 4 255) secp256k1ModulusBits 560 561 562 2
/-- The complete arithmetic state of production parity correction. -/
def secp256k1EEAParityIdealState (s : BasisState) : BasisState :=
  eeaParityCorrectionIdealState (List.range' 263 256) secp256k1ModulusBits 2 s
private theorem parity_layout :
    ([2,560,561,562]++List.range' 263 256++List.range' 4 255).Nodup := by
  simp only [List.nodup_append]
  refine ⟨⟨by decide,List.nodup_range',?_⟩,List.nodup_range',?_⟩
  all_goals
    intro a ha b hb he
    simp at ha hb
    omega
/-- Every actual parity-correction branch realizes the same full state with positive amplitude. -/
theorem secp256k1EEAParityCorrection_branch (s : BasisState)
    (hc : s 560=false) (hr : s 561=false) (ht : s 562=false)
    (branch : InstrumentBranch) (hb : branch∈secp256k1EEAParityCorrection.run) :
    branch.kraus (ket s)=registerXResetMagnitude branch.history.length •
      ket (secp256k1EEAParityIdealState s) := by
  exact eeaParityCorrection_branch_correct _ _ _ _ _ _ _ s (by simp [secp256k1ModulusBits])
    (by simp) parity_layout hc hr ht branch hb
private theorem parity_constantBits_take (width count value : Nat) :
    (constantBits width value).take count=constantBits (min count width) value := by
  induction width generalizing count value with
  | zero => simp [constantBits,xorConstantBits]
  | succ width ih =>
    cases count with
    | zero => simp [constantBits,xorConstantBits]
    | succ count =>
      have h := ih count (value/2)
      simp only [constantBits] at h ⊢
      rw [Nat.succ_min_succ]
      simp only [List.replicate_succ,xorConstantBits]
      split <;> simp only [List.take_succ_cons,h]
/-- After the full EEA and canonicalization prefix, parity correction produces the modular inverse and restores the borrowed epoch and scratch. -/
theorem secp256k1EEAParity_inverse (s : BasisState)
    (hclean : Clean (List.range' 0 263++List.range' 519 61) s)
    (hx : 0 < boolWordToNat (wireValues (List.range' 263 256) s))
    (hxp : boolWordToNat (wireValues (List.range' 263 256) s)<ShorECDLP.p) :
    let before := run (secp256k1EEAForwardUnitary indexedStepProductionRegisters ++
      canonicalWork2Rotation ++ terminalEpochCompression) (eeaPreprocessIdealState s)
    let out := secp256k1EEAParityIdealState before
    boolWordToNat (wireValues (List.range' 263 256) out)=
      paperInverse ShorECDLP.p (boolWordToNat (wireValues (List.range' 263 256) s)) ∧
    (boolWordToNat (wireValues (List.range' 263 256) out) : ZMod ShorECDLP.p) *
      (boolWordToNat (wireValues (List.range' 263 256) s) : ZMod ShorECDLP.p)=1 ∧
    out 559=false ∧ IndexedStepReady indexedStepProductionRegisters out := by
  let initial := paperInitial ShorECDLP.p (boolWordToNat (wireValues (List.range' 263 256) s))
  let canonical := run canonicalWork2Rotation (run (secp256k1EEAForwardUnitary indexedStepProductionRegisters)
    (eeaPreprocessIdealState s))
  let before := run terminalEpochCompression canonical
  have hfull := secp256k1EEAForward_canonical_epoch s hclean hx hxp
  have hcan := secp256k1EEAForward_canonical_coefficient s hclean hx hxp
  have hinv := paperRun_preservesInvariant (paperInitial_invariant ShorECDLP.Secp256k1.p_prime hx hxp)
  have hbank : wireValues (List.range' 263 259) before=constantBits 259 (paperRun initial).tPrime := by
    simpa only [Classical.run_append] using hfull.1
  have hbits : wireValues (List.range' 263 256) before=constantBits 256 (paperRun initial).tPrime := by
    have h := congrArg (List.take 256) hbank
    rw [parity_constantBits_take] at h
    simpa only [wireValues,←List.map_take,List.take_range'_of_length_ge (by decide : 259≥256),Nat.min_eq_left (by decide : 256≤259)] using h
  have hvalue : boolWordToNat (wireValues (List.range' 263 256) before)=(paperRun initial).tPrime := by
    rw [hbits,boolWordToNat_constantBits,Nat.mod_eq_of_lt]
    exact hinv.tPrime_le.trans_lt (by norm_num [ShorECDLP.p])
  have hcontrol : canonical 558=false := by
    have hc := canonicalWork2Rotation_correct (paperPadding initial)
      (secp256k1_paperPadding_le_596 hx hxp) _ (secp256k1EEAForward_terminalState s hclean hx hxp)
      _ (secp256k1EEAForward_payload s hclean hx hxp).2.1
    exact (hc.2 558 (by decide)).trans ((secp256k1EEAForward_terminalState s hclean hx hxp).ready _ (by decide))
  have hscratch : canonical 560=false := by
    have hc := canonicalWork2Rotation_correct (paperPadding initial)
      (secp256k1_paperPadding_le_596 hx hxp) _ (secp256k1EEAForward_terminalState s hclean hx hxp)
      _ (secp256k1EEAForward_payload s hclean hx hxp).2.1
    exact (hc.2 560 (by decide)).trans ((secp256k1EEAForward_terminalState s hclean hx hxp).ready _ (by decide))
  have hcompression := terminalEpochCompression_numeric canonical hscratch hcontrol
  have hcanIter : canonical 2=(paperRun initial).iter := by simpa only [Classical.run_append] using hcan.2.2.1
  have hiter : before 2=(paperRun initial).iter := (hcompression.2 2 (by decide)).trans hcanIter
  have hp := eeaParityCorrectionIdealState_correct (List.range' 263 256) secp256k1ModulusBits
    ShorECDLP.p 2 before (by simp) (by simp [secp256k1ModulusBits]) List.nodup_range'
    (by simp) (by norm_num [ShorECDLP.p]) (by exact gidneyCompareBits_value 256 _ (by norm_num [ShorECDLP.p]))
    (by rw [hvalue];exact hinv.tPrime_le)
  have hready : IndexedStepReady indexedStepProductionRegisters before := by
    simpa only [Classical.run_append] using hfull.2.2
  have hepoch : before 559=false := by simpa only [Classical.run_append] using hfull.2.1
  have hresult : boolWordToNat (wireValues (List.range' 263 256) (secp256k1EEAParityIdealState before))=
      paperInverse ShorECDLP.p (boolWordToNat (wireValues (List.range' 263 256) s)) := by
    change boolWordToNat (wireValues (List.range' 263 256) (eeaParityCorrectionIdealState _ _ _ before))=_
    rw [hp.1,hvalue,hiter]
    rfl
  dsimp only
  rw [Classical.run_append,Classical.run_append]
  refine ⟨hresult,?_,(hp.2 _ (by simp)).trans hepoch,?_⟩
  · rw [hresult]
    exact paperRun_inverse_mod_prime ShorECDLP.Secp256k1.p_prime hx hxp
  · intro w hw
    exact (hp.2 w ((by decide : ∀ w∈indexedStepProductionRegisters.sharedScratch,w∉List.range' 263 256) w hw)).trans (hready w hw)

/-- All gates in production parity correction have distinct operands. -/
theorem secp256k1EEAParityCorrection_wellFormed : secp256k1EEAParityCorrection.WellFormed := by
  have hc := controlledConstMinus_wellFormed (List.range' 263 256) (List.range' 4 255)
    secp256k1ModulusBits 2 560 561 562 (by simp [secp256k1ModulusBits]) (by simp) parity_layout
  exact ⟨by simp [CircuitWellFormed,Gate.WellFormed],hc.seq ⟨by simp [CircuitWellFormed,Gate.WellFormed],trivial⟩⟩

/-- Production parity correction restores every wire outside the coefficient, without a value precondition. -/
theorem secp256k1EEAParityIdealState_preservesOutside (s : BasisState) (w : Wire)
    (hw : w∉List.range' 263 256) : secp256k1EEAParityIdealState s w=s w := by
  let input := List.range' 263 256
  let flipped := s[2 ↦ !s 2]
  let complemented : BasisState := fun v => if v∈input then flipped v ^^ flipped 2 else flipped v
  let increment := ((List.range input.length).map (Nat.testBit 1))
  let first := gidneyAddIdealState input increment 2 complemented
  let after := gidneyAddIdealState input secp256k1ModulusBits 2 first
  have hfirst : ∀ v∉input,first v=complemented v :=
    (gidneyAddIdealState_correct input increment 2 complemented (by simp [increment]) List.nodup_range').2
  have hafter : ∀ v∉input,after v=first v :=
    (gidneyAddIdealState_correct input secp256k1ModulusBits 2 first (by simp [input,secp256k1ModulusBits]) List.nodup_range').2
  have hframe : ∀ v∉input,after v=flipped v := by
    intro v hv
    rw [hafter v hv,hfirst v hv]
    simp only [complemented,if_neg hv]
  have hflag : after 2= !s 2 := (hframe 2 (by simp [input])).trans (by simp [flipped])
  change (after[2 ↦ !after 2]) w=s w
  by_cases h : w=2
  · subst w; simp [hflag]
  · rw [upd_other _ _ _ h,hframe w hw]
    exact upd_other _ _ _ h

end
end ShorECDLP.Paper2607_13816
