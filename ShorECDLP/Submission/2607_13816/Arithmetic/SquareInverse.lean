import ShorECDLP.Submission.«2607_13816».Arithmetic.Square
import ShorECDLP.Submission.«2607_13816».Arithmetic.HornerInverse
/-!
# Source inverse squaring

The literal low-to-high copied subtraction / halving schedule reverses the
existing forward square. Every pair of measurement branches restores the whole
input state, with an amplitude determined only by the two history lengths.
-/
namespace ShorECDLP.Paper2607_13816
open Classical
/-- Literal copied-control subtraction from the source inverse square. -/
def squareSub (input acc : List Wire) (modulus : List Bool) (p : Nat)
    (bit copied c r t f : Wire) : Quantum.AdaptiveCircuit :=
  .unitary [.CX bit copied] ((controlledModularSub input acc modulus p copied c r t f).seq
    (.unitary [.CX bit copied] .done))
private theorem copy_twice (bit copied : Wire) (s : BasisState) (hne : bit≠copied) :
    run [.CX bit copied] (run [.CX bit copied] s)=s := by
  funext w
  by_cases hw : w=copied
  · subst w
    simp [run,applyGate,upd,hne]
  · simp [run,applyGate,upd,hw]
private theorem copy_word (ws : List Wire) (bit copied : Wire) (s : BasisState)
    (hn : copied ∉ ws) : wireValues ws (run [.CX bit copied] s)=wireValues ws s := by
  apply List.map_congr_left
  intro w hw
  have hne : w≠copied := fun he => hn (he ▸ hw)
  simp [run,applyGate,upd,hne]
private theorem square_copy_geometry (input acc : List Wire) (bit copied c r t f : Wire)
    (hbit : bit ∈ input) (hnd : ([copied,c,r,t,f]++input++acc).Nodup) :
    bit≠copied ∧ copied ∉ input ∧ copied ∉ acc ∧ ∀ w ∈ [c,r,t,f], w≠copied := by
  have hn : copied ∉ [c,r,t,f]++input++acc := (List.nodup_cons.mp hnd).1
  have hi : copied ∉ input := fun h => hn (by simp [h])
  refine ⟨fun he => hi (he ▸ hbit),hi,fun h => hn (by simp [h]),?_⟩
  intro w hw he
  subst w
  exact hn (by simp only [List.mem_append]; exact Or.inl (Or.inl hw))

theorem squareSub_after_add (input acc : List Wire) (correction modulus : List Bool) (p : Nat)
    (bit copied c r t f : Wire) (s : BasisState)
    (hbit : bit ∈ input) (hlen : input.length=acc.length) (hne : 0<acc.length)
    (hk : acc.length=correction.length) (hm : acc.length=modulus.length)
    (hnd : ([copied,c,r,t,f]++input++acc).Nodup)
    (hc : s c=false) (hr : s r=false) (ht : s t=false) (hf : s f=false)
    (hp : p<2^acc.length) (hx : boolWordToNat (wireValues input s)<p)
    (hy : boolWordToNat (wireValues acc s)<p)
    (hconstant : boolWordToNat correction=2^acc.length-p) (hmodulus : boolWordToNat modulus=p)
    (branch : Quantum.InstrumentBranch)
    (hb : branch ∈ (squareSub input acc modulus p bit copied c r t f).run) :
    branch.kraus (Quantum.ket (squareAddIdealState input acc correction p bit copied c f s)) =
      Quantum.registerXResetMagnitude branch.history.length • Quantum.ket s := by
  have hg := square_copy_geometry input acc bit copied c r t f hbit hnd
  let before := run [.CX bit copied] s
  have hclean (w : Wire) (hw : w ∈ [c,r,t,f]) : before w=s w := by
    have hn := hg.2.2.2 w hw
    simp [before,run,applyGate,upd,hn]
  obtain ⟨after,ha,hh,hbranch⟩ := gidneyUnitaryBranch [.CX bit copied] _ branch hb
  simp only [Quantum.AdaptiveCircuit.run_seq,Quantum.Instrument.seq,List.mem_flatMap,List.mem_map,
    Quantum.AdaptiveCircuit.run_unitary_done,List.mem_singleton] at ha
  obtain ⟨subBranch,hsubBranch,last,rfl,rfl⟩ := ha
  have hsub := modularSub_branch_after_add input acc correction modulus p copied c r t f before
    hlen hne hk hm hnd ((hclean c (by simp)).trans hc) ((hclean r (by simp)).trans hr)
    ((hclean t (by simp)).trans ht) ((hclean f (by simp)).trans hf) hp
    (by rw [copy_word input bit copied s hg.2.1]; exact hx)
    (by rw [copy_word acc bit copied s hg.2.2.1]; exact hy) hconstant hmodulus subBranch hsubBranch
  rw [hbranch]
  simp only [Quantum.InstrumentBranch.seq,LinearMap.comp_apply]
  rw [Quantum.run_ket_agrees_classical _ _ (by simp)]
  simp only [squareAddIdealState,copy_twice bit copied _ hg.1]
  rw [hsub,map_smul,Quantum.run_ket_agrees_classical _ _ (by simp)]
  rw [show run [.CX bit copied] before=s from copy_twice bit copied s hg.1]
  rw [hh]
  simp only [Quantum.InstrumentBranch.seq,List.length_append,List.length_nil,Nat.add_zero]

private theorem square_inverse_double_layout (input acc : List Wire) (copied c r t f : Wire)
    (hnd : ([copied,c,r,t,f]++input++acc).Nodup) : ([f,r,t,c]++acc++input).Nodup := by
  exact horner_double_layout [] input acc c r t f (List.nodup_cons.mp hnd).2

theorem squareSub_wellFormed (input acc : List Wire) (modulus : List Bool) (p : Nat)
    (bit copied c r t f : Wire) (hbit : bit ∈ input)
    (hlen : input.length=acc.length) (hne : 0<acc.length) (hm : acc.length=modulus.length)
    (hnd : ([copied,c,r,t,f]++input++acc).Nodup) :
    (squareSub input acc modulus p bit copied c r t f).WellFormed := by
  have hg := square_copy_geometry input acc bit copied c r t f hbit hnd
  have hc : CircuitWellFormed [.CX bit copied] := by
    intro g h; simp only [List.mem_singleton] at h; subst g; exact hg.1
  exact ⟨hc,(controlledModularSub_wellFormed input acc modulus p copied c r t f hlen hne hm hnd).seq ⟨hc,trivial⟩⟩
/-- The source visits bits from least significant upward, subtracting before halving. -/
def squareLoopInverse (controls input acc : List Wire) (modulus : List Bool) (p : Nat)
    (copied c r t f : Wire) : Quantum.AdaptiveCircuit :=
  match controls with
  | [] => .done
  | bit::bits => (squareSub input acc modulus p bit copied c r t f).seq
      (if bits=[] then .done else (modularHalve acc input modulus p f r t c).seq
        (squareLoopInverse bits input acc modulus p copied c r t f))

theorem squareLoopInverse_wellFormed (controls input : List Wire) (a : Wire) (rest : List Wire)
    (modulus : List Bool) (p : Nat) (copied c r t f : Wire)
    (hlen : input.length=(a::rest).length) (hm : (a::rest).length=modulus.length)
    (hnd : ([copied,c,r,t,f]++input++(a::rest)).Nodup)
    (hcontrols : ∀ bit ∈ controls, bit ∈ input) :
    (squareLoopInverse controls input (a::rest) modulus p copied c r t f).WellFormed := by
  induction controls with
  | nil => trivial
  | cons bit bits ih =>
    apply Quantum.AdaptiveCircuit.WellFormed.seq
    · exact squareSub_wellFormed input (a::rest) modulus p bit copied c r t f
        (hcontrols bit (by simp)) hlen (by simp) hm hnd
    · by_cases hz : bits=[]
      · simp only [if_pos hz]; trivial
      · simp only [if_neg hz]
        exact (modularHalve_wellFormed a rest input modulus p f r t c hm hlen.symm
          (square_inverse_double_layout input (a::rest) copied c r t f hnd)).seq
          (ih (fun w hw => hcontrols w (List.mem_cons_of_mem bit hw)))
theorem squareLoopInverse_after_forward (controls input : List Wire) (a : Wire) (rest : List Wire)
    (correction modulus : List Bool) (p : Nat) (copied c r t f : Wire) (s : BasisState)
    (hlen : input.length = (a :: rest).length) (hk : (a :: rest).length = correction.length)
    (hm : (a :: rest).length = modulus.length)
    (hnd : ([copied,c,r,t,f] ++ input ++ (a :: rest)).Nodup)
    (hcontrols : ∀ bit ∈ controls, bit ∈ input)
    (hcopy : s copied=false) (hc : s c = false) (hr : s r = false) (ht : s t = false) (hf : s f = false)
    (hp : p < 2 ^ (a :: rest).length) (hodd : p % 2 = 1)
    (hx : boolWordToNat (wireValues input s) < p)
    (hzero : boolWordToNat (wireValues (a :: rest) s) = 0)
    (hconstant : boolWordToNat correction = 2 ^ (a :: rest).length - p)
    (hmodulus : boolWordToNat modulus = p)
    (branch : Quantum.InstrumentBranch)
    (hb : branch ∈ (squareLoopInverse controls input (a :: rest) modulus p copied c r t f).run) :
    branch.kraus (Quantum.ket (squareLoopIdealState controls input (a :: rest) correction p copied c f s)) =
      Quantum.registerXResetMagnitude branch.history.length • Quantum.ket s := by
  have hp0 : 0 < p := by omega
  induction controls generalizing branch with
  | nil =>
    have hd := gidneyDoneBranch branch hb
    rw [hd.2,hd.1]
    simp [Quantum.registerXResetMagnitude,squareLoopIdealState]
  | cons q qs ih =>
    have htail : ∀ bit ∈ qs, bit ∈ input := fun w hw => hcontrols w (List.mem_cons_of_mem q hw)
    have hbit : q ∈ input := hcontrols q (by simp)
    by_cases hqs : qs = []
    · subst qs
      have hsub := squareSub_after_add input (a :: rest) correction modulus p q copied c r t f s
        hbit hlen (by simp) hk hm hnd hc hr ht hf hp hx (by omega) hconstant hmodulus
      apply horner_seq_branch _ .done _ s s hsub ?_ branch hb
      intro b hb
      have hd := gidneyDoneBranch b hb
      rw [hd.2,hd.1]
      simp [Quantum.registerXResetMagnitude]
    · let before := squareLoopIdealState qs input (a :: rest) correction p copied c f s
      let doubled := modularDoubleIdealState (a :: rest) correction p c before
      have hi := squareLoopIdealState_correct qs input a rest correction p copied c r t f s
        hlen hk hnd htail hcopy hc hf hp hodd hx hzero hconstant
      have hg (w : Wire) (hw : w ∈ [copied,c,r,t,f] ++ input) : w ∉ a::rest := by
        intro hh
        exact (List.nodup_append.mp hnd).2.2 w hw w hh rfl
      have hframe (w : Wire) (hw : w ∈ [copied,c,r,t,f] ++ input) : before w = s w := hi.2 w (hg w hw)
      have hvalue : boolWordToNat (wireValues (a :: rest) before) < p := by
        rw [hi.1]; exact Nat.mod_lt _ hp0
      have hdLayout := square_inverse_double_layout input (a :: rest) copied c r t f hnd
      have hshort := (doubling_layout (a :: rest) input f r t c hdLayout).1
      have hd := modularDoubleIdealState_correct a c rest correction p before hshort
        ((hframe c (by simp)).trans hc) hk hp hvalue hodd hconstant
      have hdframe (w : Wire) (hw : w ∈ [copied,c,r,t,f] ++ input) : doubled w = s w :=
        (hd.2 w (hg w hw)).trans (hframe w hw)
      have hdvalue : boolWordToNat (wireValues (a :: rest) doubled) < p := by
        rw [hd.1]; exact Nat.mod_lt _ hp0
      have hdinput : wireValues input doubled = wireValues input s :=
        List.map_congr_left (fun w hw => hdframe w (by simp [hw]))
      have hsub := squareSub_after_add input (a :: rest) correction modulus p q copied c r t f doubled
        hbit hlen (by simp) hk hm hnd ((hdframe c (by simp)).trans hc)
        ((hdframe r (by simp)).trans hr) ((hdframe t (by simp)).trans ht)
        ((hdframe f (by simp)).trans hf) hp (by rw [hdinput]; exact hx) hdvalue hconstant hmodulus
      have hhalve := modularHalve_branch_after_double a rest input correction modulus p f r t c before
        hk hm hlen.symm hdLayout ((hframe f (by simp)).trans hf)
        ((hframe r (by simp)).trans hr) ((hframe t (by simp)).trans ht)
        ((hframe c (by simp)).trans hc) hp hvalue hodd hconstant hmodulus
      simp only [squareLoopInverse,if_neg hqs] at hb
      change branch.kraus (Quantum.ket (squareAddIdealState input (a :: rest) correction p q copied c f (if qs = [] then before else doubled))) = _
      rw [if_neg hqs]
      apply horner_seq_branch _ _ _ doubled s hsub ?_ branch hb
      intro b hb
      exact horner_seq_branch _ _ doubled before s hhalve (fun b hb => ih htail b hb) b hb


private theorem squareSub_counts (q copied c r t f : Wire) :
    let g := squareSub (List.range' 260 256) (List.range' 4 256)
      secp256k1ModulusBits (2 ^ 256 - (2 ^ 32 + 977)) q copied c r t f
    gidneyToffoliCount g = 2813 ∧ gidneyCnotCount g = 7352 ∧ g.tCount = 19691 ∧ g.measurementCount = 511 := by
  have ha := secp256k1ModularSub_counts copied c r t f
  have hw := squareWrap_counts ([.CX q copied] : Circuit) ([.CX q copied] : Circuit)
    (controlledModularSub (List.range' 260 256) (List.range' 4 256)
      secp256k1ModulusBits (2 ^ 256 - (2 ^ 32 + 977)) copied c r t f)
  dsimp only
  exact ⟨hw.1.trans (by rw [ha.1]; rfl),hw.2.1.trans (by rw [ha.2.1]; rfl),
    hw.2.2.1.trans (by rw [ha.2.2.1]; rfl),hw.2.2.2.trans ha.2.2.2⟩

private theorem inverseSquare_counts (controls : List Wire) (copied c r t f : Wire) :
    let g := squareLoopInverse controls (List.range' 260 256) (List.range' 4 256)
      secp256k1ModulusBits (2 ^ 256 - (2 ^ 32 + 977)) copied c r t f
    gidneyToffoliCount g = controls.length * 2813 + (controls.length - 1) * 1531 ∧
    gidneyCnotCount g = controls.length * 7352 + (controls.length - 1) * 6070 ∧
    g.tCount = controls.length * 19691 + (controls.length - 1) * 10717 ∧
    g.measurementCount = (controls.length * 2 - 1) * 511 := by
  have hseqT (a b : Quantum.AdaptiveCircuit) : (a.seq b).tCount = a.tCount + b.tCount := by
    simpa only [gidneyGateCount_tCount] using modularGateCount_seq tCost a b
  have hseqCCX (a b : Quantum.AdaptiveCircuit) : gidneyToffoliCount (a.seq b) =
      gidneyToffoliCount a + gidneyToffoliCount b := modularGateCount_seq _ a b
  have hseqCX (a b : Quantum.AdaptiveCircuit) : gidneyCnotCount (a.seq b) =
      gidneyCnotCount a + gidneyCnotCount b := modularGateCount_seq _ a b
  induction controls with
  | nil => simp [squareLoopInverse,gidneyToffoliCount,gidneyCnotCount,gidneyGateCount,
      Quantum.AdaptiveCircuit.tCount,Quantum.AdaptiveCircuit.measurementCount]
  | cons q qs ih =>
    have ha := squareSub_counts q copied c r t f
    have hd := secp256k1ModularHalve_counts f r t c
    dsimp only at ih ha hd ⊢
    rw [squareLoopInverse]
    by_cases hz : qs = []
    · rw [if_pos hz]
      simp only [hseqCCX,hseqCX,hseqT,modularMeasurements_seq,
        ha.1,ha.2.1,ha.2.2.1,ha.2.2.2]
      subst qs
      simp [gidneyToffoliCount,gidneyCnotCount,gidneyGateCount,
        Quantum.AdaptiveCircuit.tCount,Quantum.AdaptiveCircuit.measurementCount]
    · rw [if_neg hz]
      simp only [hseqCCX,hseqCX,hseqT,modularMeasurements_seq,ih.1,ih.2.1,ih.2.2.1,ih.2.2.2,
        ha.1,ha.2.1,ha.2.2.1,ha.2.2.2,hd.1,hd.2.1,hd.2.2.1,hd.2.2.2,List.length_cons]
      have hn : qs.length ≠ 0 := fun h => hz (List.eq_nil_of_length_eq_zero h)
      omega

private theorem squareSub_wires (bit q c r t f w : Wire) :
    w ∈ (squareSub (List.range' 260 256) (List.range' 4 256)
      secp256k1ModulusBits (2^256-(2^32+977)) bit q c r t f).wires ↔
    w ∈ [bit,q,c,r,t,f]++List.range' 4 256++List.range' 260 256 := by
  simp only [squareSub,Quantum.AdaptiveCircuit.wires,modularWires_seq,modularSub256_wires_iff,
    circuitWires,List.flatMap_cons,List.flatMap_nil,gateWires,List.append_nil,
    List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  tauto

private theorem inverseSquare_wires (controls : List Wire) (copied c r t f w : Wire) :
    w ∈ (squareLoopInverse controls (List.range' 260 256) (List.range' 4 256)
      secp256k1ModulusBits (2 ^ 256 - (2 ^ 32 + 977)) copied c r t f).wires ↔
      w ∈ controls ∨ (controls ≠ [] ∧ w ∈ [copied,c,r,t,f] ++ List.range' 4 256 ++ List.range' 260 256) := by
  induction controls with
  | nil => simp [squareLoopInverse,Quantum.AdaptiveCircuit.wires]
  | cons q qs ih =>
    rw [squareLoopInverse,modularWires_seq,squareSub_wires]
    by_cases hz : qs = []
    · rw [if_pos hz]
      subst qs
      simp only [Quantum.AdaptiveCircuit.wires,List.mem_cons,List.not_mem_nil,List.mem_append,
        or_false,List.cons_ne_nil,ne_eq,not_false_eq_true,true_and]
      tauto
    · rw [if_neg hz,modularWires_seq,modularHalve256_wires_iff,ih]
      simp only [hz,not_false_eq_true,true_and,List.mem_cons,List.mem_append,List.not_mem_nil,or_false,
        List.cons_ne_nil,ne_eq]
      tauto

attribute [local irreducible] squareLoopInverse squareLoop squareLoopIdealState wireValues boolWordToNat
/-- The actual source inverse square, on the same 517 physical wires as the forward square. -/
def secp256k1SquareInverse : Quantum.AdaptiveCircuit :=
  squareLoopInverse (List.range' 260 256) (List.range' 260 256) (List.range' 4 256)
    secp256k1ModulusBits (2^256-(2^32+977)) 516 1 2 3 0
private theorem inverseSquare_layout :
    ([516,1,2,3,0]++List.range' 260 256++(4::List.range' 5 255)).Nodup := by
  change ([516,1,2,3,0]++List.range' 260 256++List.range' 4 256 : List Nat).Nodup
  simp only [List.nodup_append]
  refine ⟨⟨by decide,List.nodup_range',?_⟩,List.nodup_range',?_⟩
  all_goals
    intro a ha b hb he
    simp at ha hb
    omega
private theorem inverseSquare_qubits : secp256k1SquareInverse.qubitCount = 517 := by
  have heq : secp256k1SquareInverse.wires.dedup.toFinset = (List.range' 0 517).toFinset := by
    ext w
    simp only [List.mem_toFinset,List.mem_dedup,secp256k1SquareInverse,inverseSquare_wires]
    have hn : List.range' 260 256 ≠ [] := by decide +kernel
    simp [hn]
    dsimp only [Wire] at *
    omega
  have hc := congrArg Finset.card heq
  simpa only [List.toFinset_card_of_nodup (List.nodup_dedup _),
    List.toFinset_card_of_nodup (List.nodup_range'),List.length_range'] using hc

/-- Same-circuit inverse certificate: every pair of actual forward and inverse
branches restores the complete input state with a positive history-only coefficient.
The inverse has normalized mass and the listed exact production resources. -/
theorem secp256k1SquareInverse_correct_resources (s : BasisState)
    (hcopy : s 516=false) (hc : s 1 = false) (hr : s 2 = false) (ht : s 3 = false) (hf : s 0 = false)
    (hx : boolWordToNat (wireValues (List.range' 260 256) s) < 2 ^ 256 - (2 ^ 32 + 977))
    (hzero : boolWordToNat (wireValues (List.range' 4 256) s) = 0) :
    (∀ forward ∈ secp256k1Square.run, ∀ inverse ∈ secp256k1SquareInverse.run,
      inverse.kraus (forward.kraus (Quantum.ket s)) =
        Quantum.registerXResetMagnitude (forward.history.length + inverse.history.length) • Quantum.ket s) ∧
    (∀ ψ, Quantum.Instrument.bornMass secp256k1SquareInverse.run ψ = Quantum.normSq ψ) ∧
    secp256k1SquareInverse.WellFormed ∧
    gidneyToffoliCount secp256k1SquareInverse = 1110533 ∧
    gidneyCnotCount secp256k1SquareInverse = 3429962 ∧
    secp256k1SquareInverse.tCount = 7773731 ∧
    secp256k1SquareInverse.measurementCount = 261121 ∧
    secp256k1SquareInverse.qubitCount = 517 := by
  have hlen : (List.range' 260 256).length = (4 :: List.range' 5 255).length := by simp
  have hk : (4 :: List.range' 5 255).length = secp256k1ReductionConstantBits.length := by simp [secp256k1ReductionConstantBits]
  have hm : (4 :: List.range' 5 255).length = secp256k1ModulusBits.length := by simp [secp256k1ModulusBits]
  have hp : 2 ^ 256 - (2 ^ 32 + 977) < 2 ^ (4 :: List.range' 5 255).length := by
    simp only [List.length_cons,List.length_range']; decide +kernel
  have hodd : (2 ^ 256 - (2 ^ 32 + 977)) % 2 = 1 := by decide +kernel
  have hv : boolWordToNat secp256k1ReductionConstantBits =
      2 ^ (4 :: List.range' 5 255).length - (2 ^ 256 - (2 ^ 32 + 977)) := by
    rw [secp256k1ReductionConstant_value]; simp only [List.length_cons,List.length_range']; decide +kernel
  have hmod : boolWordToNat secp256k1ModulusBits = 2 ^ 256 - (2 ^ 32 + 977) := by decide +kernel
  have hw : secp256k1SquareInverse.WellFormed := squareLoopInverse_wellFormed
    (List.range' 260 256) (List.range' 260 256) 4 (List.range' 5 255) _ _ 516 1 2 3 0 hlen hm inverseSquare_layout (fun _ h => h)
  have hn := inverseSquare_counts (List.range' 260 256) 516 1 2 3 0
  refine ⟨?_,fun ψ => Quantum.AdaptiveCircuit.run_preservesBornMass _ hw ψ,hw,
    ?_,?_,?_,?_,inverseSquare_qubits⟩
  · intro forward hforward inverse hinverse
    have hfw := squareLoop_branch_correct (List.range' 260 256) (List.range' 260 256) 4 (List.range' 5 255)
      _ _ 516 1 2 3 0 s hlen hk inverseSquare_layout (fun _ h => h) hcopy hc hr ht hf (by simpa only [List.length_cons,List.length_range'] using hp) hodd hx hzero (by simpa only [List.length_cons,List.length_range'] using hv) forward hforward
    have hiv := squareLoopInverse_after_forward (List.range' 260 256) (List.range' 260 256) 4 (List.range' 5 255)
      _ _ _ 516 1 2 3 0 s hlen hk hm inverseSquare_layout (fun _ h => h) hcopy hc hr ht hf (by simpa only [List.length_cons,List.length_range'] using hp) hodd hx hzero (by simpa only [List.length_cons,List.length_range'] using hv) hmod inverse hinverse
    rw [hfw,map_smul,hiv]
    simp only [smul_smul,Quantum.registerXResetMagnitude,← pow_add]
  · simpa only [List.length_range'] using hn.1
  · simpa only [List.length_range'] using hn.2.1
  · simpa only [List.length_range'] using hn.2.2.1
  · simpa only [List.length_range'] using hn.2.2.2

end ShorECDLP.Paper2607_13816
