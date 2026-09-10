import ShorECDLP.Submission.«2607_13816».Arithmetic.HornerMul
import ShorECDLP.Submission.«2607_13816».Arithmetic.Halving

/-!
# Source inverse Horner multiplication

Subtraction and halving run from the low multiplier bit upward, reversing the
forward stage order while retaining the source's exchanged carry/flag roles.
-/
namespace ShorECDLP.Paper2607_13816
open Classical
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-- Source `append_mul_zero_dbladd_inverse_quadratic`, with fresh measured inverse
arithmetic stages rather than an adjoint of an adaptive program. -/
def hornerMulInverse (controls input acc : List Wire) (modulus : List Bool) (p : Nat)
    (c r t f : Wire) : Quantum.AdaptiveCircuit :=
  match controls with
  | [] => .done
  | q :: qs => (controlledModularSub input acc modulus p q c r t f).seq
      (if qs = [] then .done else
        (modularHalve acc input modulus p f r t c).seq
          (hornerMulInverse qs input acc modulus p c r t f))

/-- The inverse reuses the forward physical layout at every stage. -/
theorem hornerMulInverse_wellFormed (controls input : List Wire) (a : Wire) (rest : List Wire)
    (modulus : List Bool) (p : Nat) (c r t f : Wire)
    (hlen : input.length = (a :: rest).length) (hm : (a :: rest).length = modulus.length)
    (hnd : ([c,r,t,f] ++ controls ++ input ++ (a :: rest)).Nodup) :
    (hornerMulInverse controls input (a :: rest) modulus p c r t f).WellFormed := by
  induction controls with
  | nil => trivial
  | cons q qs ih =>
    apply Quantum.AdaptiveCircuit.WellFormed.seq
    · exact controlledModularSub_wellFormed input (a :: rest) modulus p q c r t f hlen
        (by simp) hm (horner_add_layout q qs input (a :: rest) c r t f hnd)
    · by_cases hqs : qs = []
      · simp only [if_pos hqs]; trivial
      · simp only [if_neg hqs]
        exact Quantum.AdaptiveCircuit.WellFormed.seq
          (modularHalve_wellFormed a rest input modulus p f r t c hm hlen.symm
            (horner_double_layout (q :: qs) input (a :: rest) c r t f hnd))
          (ih (horner_tail_layout q qs input (a :: rest) c r t f hnd))

theorem modularSub_branch_after_add (input acc : List Wire) (correction modulus : List Bool)
    (p : Nat) (q c r t f : Wire) (s : BasisState)
    (hlen : input.length = acc.length) (hne : 0 < acc.length)
    (hk : acc.length = correction.length) (hm : acc.length = modulus.length)
    (hnd : ([q,c,r,t,f] ++ input ++ acc).Nodup)
    (hc : s c = false) (hr : s r = false) (ht : s t = false) (hf : s f = false)
    (hp : p < 2 ^ acc.length) (hx : boolWordToNat (wireValues input s) < p)
    (hy : boolWordToNat (wireValues acc s) < p)
    (hconstant : boolWordToNat correction = 2 ^ acc.length - p)
    (hmodulus : boolWordToNat modulus = p)
    (branch : Quantum.InstrumentBranch)
    (hb : branch ∈ (controlledModularSub input acc modulus p q c r t f).run) :
    branch.kraus (Quantum.ket (modularAddIdealState input acc correction p q c f s)) =
      Quantum.registerXResetMagnitude branch.history.length • Quantum.ket s := by
  have ha := modularAddIdealState_correct input acc correction p q c r t f s
    hlen hk hnd hc hf hp hx hy hconstant
  have hsep := (List.nodup_append.mp hnd).2.2
  have hw (w : Wire) (h : w ∈ [q,c,r,t,f]) : w ∉ acc := by
    intro ha; exact hsep w (by simp only [List.mem_append,List.mem_cons,List.not_mem_nil] at h ⊢; tauto) w ha rfl
  have hb' := controlledModularSub_branch_correct input acc modulus p q c r t f _
    hlen hne hm hnd ((ha.2 c (hw c (by simp))).trans hc)
    ((ha.2 r (hw r (by simp))).trans hr) ((ha.2 t (hw t (by simp))).trans ht) branch hb
  have hi := modularSubIdealState_after_add input acc correction modulus p q c r t f s
    hlen hk hm hnd hc hf hp hx hy hconstant hmodulus
  rw [hb'.1,hb'.2,hi]

theorem modularHalve_branch_after_double (a : Wire) (rest dirty : List Wire)
    (correction modulus : List Bool) (p : Nat) (c r t f : Wire) (s : BasisState)
    (hk : (a :: rest).length = correction.length) (hm : (a :: rest).length = modulus.length)
    (hd : (a :: rest).length = dirty.length) (hnd : ([c,r,t,f] ++ (a :: rest) ++ dirty).Nodup)
    (hc : s c = false) (hr : s r = false) (ht : s t = false) (hf : s f = false)
    (hp : p < 2 ^ (a :: rest).length) (hx : boolWordToNat (wireValues (a :: rest) s) < p)
    (hodd : p % 2 = 1) (hconstant : boolWordToNat correction = 2 ^ (a :: rest).length - p)
    (hmodulus : boolWordToNat modulus = p)
    (branch : Quantum.InstrumentBranch)
    (hb : branch ∈ (modularHalve (a :: rest) dirty modulus p c r t f).run) :
    branch.kraus (Quantum.ket (modularDoubleIdealState (a :: rest) correction p f s)) =
      Quantum.registerXResetMagnitude branch.history.length • Quantum.ket s := by
  have hl := (doubling_layout (a :: rest) dirty c r t f hnd).1
  have ha := modularDoubleIdealState_correct a f rest correction p s hl hf hk hp hx hodd hconstant
  have hsep := (List.nodup_append.mp (List.nodup_append.mp hnd).1).2.2
  have hw (w : Wire) (h : w ∈ [c,r,t,f]) : w ∉ a :: rest := by
    intro ha; exact hsep w h w ha rfl
  have hb' := modularHalve_branch_correct a rest dirty modulus p c r t f _ hm hd hnd
    ((ha.2 c (hw c (by simp))).trans hc) ((ha.2 r (hw r (by simp))).trans hr)
    ((ha.2 t (hw t (by simp))).trans ht) branch hb
  have hi := modularHalveIdealState_after_double a f rest correction modulus p s
    hl hf hk hm hp hx hodd hconstant hmodulus
  rw [hb'.1,hb'.2,hi]

/-- Every branch of the actual inverse restores the entire zero-output input state
from the forward multiplier's product state, with a positive history-only amplitude. -/
theorem hornerMulInverse_after_forward (controls input : List Wire) (a : Wire) (rest : List Wire)
    (correction modulus : List Bool) (p : Nat) (c r t f : Wire) (s : BasisState)
    (hlen : input.length = (a :: rest).length) (hk : (a :: rest).length = correction.length)
    (hm : (a :: rest).length = modulus.length)
    (hnd : ([c,r,t,f] ++ controls ++ input ++ (a :: rest)).Nodup)
    (hc : s c = false) (hr : s r = false) (ht : s t = false) (hf : s f = false)
    (hp : p < 2 ^ (a :: rest).length) (hodd : p % 2 = 1)
    (hx : boolWordToNat (wireValues input s) < p)
    (hzero : boolWordToNat (wireValues (a :: rest) s) = 0)
    (hconstant : boolWordToNat correction = 2 ^ (a :: rest).length - p)
    (hmodulus : boolWordToNat modulus = p)
    (branch : Quantum.InstrumentBranch)
    (hb : branch ∈ (hornerMulInverse controls input (a :: rest) modulus p c r t f).run) :
    branch.kraus (Quantum.ket (hornerMulIdealState controls input (a :: rest) correction p c f s)) =
      Quantum.registerXResetMagnitude branch.history.length • Quantum.ket s := by
  have hp0 : 0 < p := by omega
  induction controls generalizing branch with
  | nil =>
    have hd := gidneyDoneBranch branch hb
    rw [hd.2,hd.1]
    simp [Quantum.registerXResetMagnitude,hornerMulIdealState]
  | cons q qs ih =>
    have htail := horner_tail_layout q qs input (a :: rest) c r t f hnd
    have haLayout := horner_add_layout q qs input (a :: rest) c r t f hnd
    by_cases hqs : qs = []
    · subst qs
      have hsub := modularSub_branch_after_add input (a :: rest) correction modulus p q c r t f s
        hlen (by simp) hk hm haLayout hc hr ht hf hp hx (by omega) hconstant hmodulus
      apply horner_seq_branch _ .done _ s s hsub ?_ branch hb
      intro b hb
      have hd := gidneyDoneBranch b hb
      rw [hd.2,hd.1]
      simp [Quantum.registerXResetMagnitude]
    · let before := hornerMulIdealState qs input (a :: rest) correction p c f s
      let doubled := modularDoubleIdealState (a :: rest) correction p c before
      have hi := hornerMulIdealState_correct qs input a rest correction p c r t f s
        hlen hk htail hc hf hp hodd hx hzero hconstant
      have hg := horner_geometry (q :: qs) input (a :: rest) c r t f hnd
      have hframe (w : Wire) (hw : w ∈ [c,r,t,f] ++ (q :: qs) ++ input) : before w = s w := hi.2 w (hg w hw)
      have hvalue : boolWordToNat (wireValues (a :: rest) before) < p := by
        rw [hi.1]; exact Nat.mod_lt _ hp0
      have hdLayout := horner_double_layout (q :: qs) input (a :: rest) c r t f hnd
      have hshort := (doubling_layout (a :: rest) input f r t c hdLayout).1
      have hd := modularDoubleIdealState_correct a c rest correction p before hshort
        ((hframe c (by simp)).trans hc) hk hp hvalue hodd hconstant
      have hdframe (w : Wire) (hw : w ∈ [c,r,t,f] ++ (q :: qs) ++ input) : doubled w = s w :=
        (hd.2 w (hg w hw)).trans (hframe w hw)
      have hdvalue : boolWordToNat (wireValues (a :: rest) doubled) < p := by
        rw [hd.1]; exact Nat.mod_lt _ hp0
      have hdinput : wireValues input doubled = wireValues input s :=
        List.map_congr_left (fun w hw => hdframe w (by simp [hw]))
      have hsub := modularSub_branch_after_add input (a :: rest) correction modulus p q c r t f doubled
        hlen (by simp) hk hm haLayout ((hdframe c (by simp)).trans hc)
        ((hdframe r (by simp)).trans hr) ((hdframe t (by simp)).trans ht)
        ((hdframe f (by simp)).trans hf) hp (by rw [hdinput]; exact hx) hdvalue hconstant hmodulus
      have hhalve := modularHalve_branch_after_double a rest input correction modulus p f r t c before
        hk hm hlen.symm hdLayout ((hframe f (by simp)).trans hf)
        ((hframe r (by simp)).trans hr) ((hframe t (by simp)).trans ht)
        ((hframe c (by simp)).trans hc) hp hvalue hodd hconstant hmodulus
      simp only [hornerMulInverse,if_neg hqs] at hb
      change branch.kraus (Quantum.ket (modularAddIdealState input (a :: rest) correction p q c f (if qs = [] then before else doubled))) = _
      rw [if_neg hqs]
      apply horner_seq_branch _ _ _ doubled s hsub ?_ branch hb
      intro b hb
      exact horner_seq_branch _ _ doubled before s hhalve (fun b hb => ih htail b hb) b hb

private theorem inverseHorner_counts (controls : List Wire) (c r t f : Wire) :
    let g := hornerMulInverse controls (List.range' 260 256) (List.range' 4 256)
      secp256k1ModulusBits (2 ^ 256 - (2 ^ 32 + 977)) c r t f
    gidneyToffoliCount g = controls.length * 2813 + (controls.length - 1) * 1531 ∧
    gidneyCnotCount g = controls.length * 7350 + (controls.length - 1) * 6070 ∧
    g.tCount = controls.length * 19691 + (controls.length - 1) * 10717 ∧
    g.measurementCount = (controls.length * 2 - 1) * 511 := by
  have hseqT (a b : Quantum.AdaptiveCircuit) : (a.seq b).tCount = a.tCount + b.tCount := by
    simpa only [gidneyGateCount_tCount] using modularGateCount_seq tCost a b
  have hseqCCX (a b : Quantum.AdaptiveCircuit) : gidneyToffoliCount (a.seq b) =
      gidneyToffoliCount a + gidneyToffoliCount b := modularGateCount_seq _ a b
  have hseqCX (a b : Quantum.AdaptiveCircuit) : gidneyCnotCount (a.seq b) =
      gidneyCnotCount a + gidneyCnotCount b := modularGateCount_seq _ a b
  induction controls with
  | nil => simp [hornerMulInverse,gidneyToffoliCount,gidneyCnotCount,gidneyGateCount,
      Quantum.AdaptiveCircuit.tCount,Quantum.AdaptiveCircuit.measurementCount]
  | cons q qs ih =>
    have ha := secp256k1ModularSub_counts q c r t f
    have hd := secp256k1ModularHalve_counts f r t c
    dsimp only at ih ha hd ⊢
    rw [hornerMulInverse]
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

private theorem inverseConstantAdd_wires (q c r t w : Wire) :
    w ∈ (controlledGidneyAddConst (List.range' 4 256) (List.range' 260 255)
      secp256k1ModulusBits q c r t).wires ↔
      w ∈ [q,c,r,t] ++ List.range' 4 256 ++ List.range' 260 255 := by
  have hb : secp256k1ModulusBits = true ::
    (List.range' 1 255).map (Nat.testBit (2 ^ 256 - 2 ^ 32 - 977)) := by decide
  rw [hb]
  exact controlledGidneyAddConst_wires 4 260 q c r t (List.range' 5 255) (List.range' 261 254)
    ((List.range' 1 255).map (Nat.testBit (2 ^ 256 - 2 ^ 32 - 977))) (by simp) (by simp) w

theorem modularSub256_wires_iff (q c r t f w : Wire) :
    w ∈ (controlledModularSub (List.range' 260 256) (List.range' 4 256)
      secp256k1ModulusBits (2 ^ 256 - (2 ^ 32 + 977)) q c r t f).wires ↔
      w ∈ [q,c,r,t,f] ++ List.range' 4 256 ++ List.range' 260 256 := by
  unfold controlledModularSub
  rw [show (List.range' 4 256).length - 1 = 255 from rfl,
    show (List.range' 260 256).take 255 = List.range' 260 255 from rfl]
  simp only [Quantum.AdaptiveCircuit.wires,List.mem_append,modularWires_seq,
    inverseConstantAdd_wires,List.not_mem_nil,or_false]
  rw [secp256k1ModularCompare_wires c r t f w]
  have hl : w ∈ circuitWires (controlledCompareLT (List.range' 4 256) (List.range' 260 256) q c f) ↔
      w ∈ [q,c,f] ++ List.range' 4 256 ++ List.range' 260 256 :=
    controlledCompareLT_wires 4 (List.range' 5 255) (List.range' 260 256) q c f w (by simp)
  rw [hl]
  have hlast : w ∈ circuitWires (controlledSubCarry (List.range' 260 256) (List.range' 4 256) q c f) →
      w ∈ [q,c,f] ++ List.range' 260 256 ++ List.range' 4 256 := by
    intro hw
    obtain ⟨g,hg,hw⟩ := List.mem_flatMap.mp hw
    exact (controlledAddCarry_usesOnly (List.range' 260 256) (List.range' 4 256) q c f).adjoint g hg w hw
  simp at hlast ⊢
  dsimp only [Wire] at *
  by_cases hmem : w ∈ circuitWires (controlledSubCarry (List.range' 260 256) (List.range' 4 256) q c f)
  · have hh := hlast hmem
    simp only [hmem,or_true,true_iff]
    omega
  · simp only [hmem,or_false]
    omega

theorem modularHalve256_wires_iff (c r t f w : Wire) :
    w ∈ (modularHalve (List.range' 4 256) (List.range' 260 256)
      secp256k1ModulusBits (2 ^ 256 - (2 ^ 32 + 977)) c r t f).wires ↔
      w ∈ [c,r,t,f] ++ List.range' 4 256 ++ List.range' 260 256 := by
  have heq : modularHalve (List.range' 4 256) (List.range' 260 256) secp256k1ModulusBits
      (2 ^ 256 - (2 ^ 32 + 977)) c r t f = .unitary [.CX 4 f]
        ((controlledGidneyAddConst (List.range' 4 256) (List.range' 260 255) secp256k1ModulusBits f c r t).seq
          ((gidneyCompareGE (List.range' 4 256) (List.range' 260 256) (2 ^ 256 - (2 ^ 32 + 977)) c r t f).seq
            (.unitary (doublingShift (List.range' 4 256) f).adjoint .done))) := rfl
  rw [heq]
  simp only [Quantum.AdaptiveCircuit.wires,List.mem_append,modularWires_seq,
    inverseConstantAdd_wires,secp256k1ModularCompare_wires,List.not_mem_nil,or_false]
  have hlast : w ∈ circuitWires (doublingShift (List.range' 4 256) f).adjoint →
      w ∈ f :: List.range' 4 256 := by
    intro hw
    obtain ⟨g,hg,hw⟩ := List.mem_flatMap.mp hw
    exact (doublingShift_usesOnly 4 f (List.range' 5 255)).adjoint g hg w hw
  have hfirst : w ∈ circuitWires [.CX 4 f] ↔ w = 4 ∨ w = f := by simp [circuitWires,gateWires]
  rw [hfirst]
  simp at hlast ⊢
  dsimp only [Wire] at *
  by_cases hmem : w ∈ circuitWires (doublingShift (List.range' 4 256) f).adjoint
  · have hh := hlast hmem
    simp only [hmem,or_true,true_iff]
    omega
  · simp only [hmem,or_false]
    omega

private theorem inverseHorner_wires (controls : List Wire) (c r t f w : Wire) :
    w ∈ (hornerMulInverse controls (List.range' 260 256) (List.range' 4 256)
      secp256k1ModulusBits (2 ^ 256 - (2 ^ 32 + 977)) c r t f).wires ↔
      w ∈ controls ∨ (controls ≠ [] ∧ w ∈ [c,r,t,f] ++ List.range' 4 256 ++ List.range' 260 256) := by
  induction controls with
  | nil => simp [hornerMulInverse,Quantum.AdaptiveCircuit.wires]
  | cons q qs ih =>
    rw [hornerMulInverse,modularWires_seq,modularSub256_wires_iff]
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

attribute [local irreducible] hornerMulInverse hornerMul hornerMulIdealState

/-- Production inverse multiplication on exactly the forward multiplier's registers. -/
def secp256k1HornerMulInverse : Quantum.AdaptiveCircuit :=
  hornerMulInverse (List.range' 516 256) (List.range' 260 256) (List.range' 4 256)
    secp256k1ModulusBits (2 ^ 256 - (2 ^ 32 + 977)) 1 2 3 0

private theorem inverseProduction_layout :
    ([1,2,3,0] ++ List.range' 516 256 ++ List.range' 260 256 ++ (4 :: List.range' 5 255)).Nodup := by
  change ([1,2,3,0] ++ List.range' 516 256 ++ List.range' 260 256 ++ List.range' 4 256 : List Nat).Nodup
  simp only [List.nodup_append]
  refine ⟨⟨⟨by decide,List.nodup_range',?_⟩,List.nodup_range',?_⟩,List.nodup_range',?_⟩
  all_goals
    intro a ha b hb he
    simp at ha hb
    omega

private theorem inverseProduction_qubits : secp256k1HornerMulInverse.qubitCount = 772 := by
  have heq : secp256k1HornerMulInverse.wires.dedup.toFinset = (List.range' 0 772).toFinset := by
    ext w
    simp only [List.mem_toFinset,List.mem_dedup,secp256k1HornerMulInverse,inverseHorner_wires]
    have hn : List.range' 516 256 ≠ [] := by decide
    simp [hn]
    dsimp only [Wire] at *
    omega
  have hc := congrArg Finset.card heq
  simpa only [List.toFinset_card_of_nodup (List.nodup_dedup _),
    List.toFinset_card_of_nodup (List.nodup_range'),List.length_range'] using hc

/-- Same-circuit inverse certificate: every pair of actual forward and inverse
branches restores the complete input state with a positive history-only coefficient.
The inverse has normalized mass and the listed exact production resources. -/
theorem secp256k1HornerMulInverse_correct_resources (s : BasisState)
    (hc : s 1 = false) (hr : s 2 = false) (ht : s 3 = false) (hf : s 0 = false)
    (hx : boolWordToNat (wireValues (List.range' 260 256) s) < 2 ^ 256 - (2 ^ 32 + 977))
    (hzero : boolWordToNat (wireValues (List.range' 4 256) s) = 0) :
    (∀ forward ∈ secp256k1HornerMul.run, ∀ inverse ∈ secp256k1HornerMulInverse.run,
      inverse.kraus (forward.kraus (Quantum.ket s)) =
        Quantum.registerXResetMagnitude (forward.history.length + inverse.history.length) • Quantum.ket s) ∧
    (∀ ψ, Quantum.Instrument.bornMass secp256k1HornerMulInverse.run ψ = Quantum.normSq ψ) ∧
    secp256k1HornerMulInverse.WellFormed ∧
    gidneyToffoliCount secp256k1HornerMulInverse = 1110533 ∧
    gidneyCnotCount secp256k1HornerMulInverse = 3429450 ∧
    secp256k1HornerMulInverse.tCount = 7773731 ∧
    secp256k1HornerMulInverse.measurementCount = 261121 ∧
    secp256k1HornerMulInverse.qubitCount = 772 := by
  have hlen : (List.range' 260 256).length = (4 :: List.range' 5 255).length := by simp
  have hk : (4 :: List.range' 5 255).length = secp256k1ReductionConstantBits.length := by simp [secp256k1ReductionConstantBits]
  have hm : (4 :: List.range' 5 255).length = secp256k1ModulusBits.length := by simp [secp256k1ModulusBits]
  have hp : 2 ^ 256 - (2 ^ 32 + 977) < 2 ^ (4 :: List.range' 5 255).length := by decide
  have hodd : (2 ^ 256 - (2 ^ 32 + 977)) % 2 = 1 := by decide
  have hv : boolWordToNat secp256k1ReductionConstantBits =
      2 ^ (4 :: List.range' 5 255).length - (2 ^ 256 - (2 ^ 32 + 977)) := by
    rw [secp256k1ReductionConstant_value]; decide
  have hmod : boolWordToNat secp256k1ModulusBits = 2 ^ 256 - (2 ^ 32 + 977) := by decide
  have hw : secp256k1HornerMulInverse.WellFormed := hornerMulInverse_wellFormed
    (List.range' 516 256) (List.range' 260 256) 4 (List.range' 5 255) _ _ 1 2 3 0 hlen hm inverseProduction_layout
  have hn := inverseHorner_counts (List.range' 516 256) 1 2 3 0
  refine ⟨?_,fun ψ => Quantum.AdaptiveCircuit.run_preservesBornMass _ hw ψ,hw,
    hn.1,hn.2.1,hn.2.2.1,hn.2.2.2,inverseProduction_qubits⟩
  intro forward hforward inverse hinverse
  have hfw := hornerMul_branch_correct (List.range' 516 256) (List.range' 260 256) 4 (List.range' 5 255)
    _ _ 1 2 3 0 s hlen hk inverseProduction_layout hc hr ht hf hp hodd hx hzero hv forward hforward
  have hiv := hornerMulInverse_after_forward (List.range' 516 256) (List.range' 260 256) 4 (List.range' 5 255)
    _ _ _ 1 2 3 0 s hlen hk hm inverseProduction_layout hc hr ht hf hp hodd hx hzero hv hmod inverse hinverse
  rw [hfw,map_smul,hiv]
  simp only [smul_smul,Quantum.registerXResetMagnitude,← pow_add]

end ShorECDLP.Paper2607_13816
