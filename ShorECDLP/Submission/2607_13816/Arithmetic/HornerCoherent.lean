import ShorECDLP.Submission.«2607_13816».Arithmetic.HornerInverse
import ShorECDLP.Framework.Quantum.CoherentRefinement
/-!
# Coherent Horner multiplication and explicit inverse

The existing exact branch theorems give positive transcript-length amplitudes.
A clean zero-input witness and physical well-formedness establish their shared
normalization once, before quantifying over inputs. These contracts support
superpositions and composition with the EEA and Figure 15 measurement cleanup.
-/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum
noncomputable section
private theorem lift_ket (f : BasisState → BasisState) (s : BasisState) :
    Finsupp.lmapDomain ℂ ℂ f (ket s) = ket (f s) := by simp [ket]
private theorem amplitude_norm (c : ℂ) (s : BasisState) :
    normSq (c • ket s) = Complex.normSq c := by
  unfold normSq
  rw [inner_smul_smul, ← Complex.normSq_eq_conj_mul_self]
  simp
private theorem coherent_branches (program : AdaptiveCircuit)
    (f : BasisState → BasisState) (Valid : BasisState → Prop)
    (hw : program.WellFormed) (witness : BasisState) (hv : Valid witness)
    (hbranch : ∀ b ∈ program.run, ∀ s, Valid s →
      b.kraus (ket s) = registerXResetMagnitude b.history.length • ket (f s)) :
    CoherentlyImplementsOn program (Finsupp.lmapDomain ℂ ℂ f) Valid := by
  refine ⟨program.run.map (fun b => registerXResetMagnitude b.history.length),?_,?_⟩
  · apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro b hb s hs
    rw [lift_ket]
    exact hbranch b hb s hs
  · have hmass := program.run_preservesBornMass hw (ket witness)
    rw [normSq_ket] at hmass
    rw [List.map_map]
    rw [← hmass]
    unfold Instrument.bornMass
    congr 1
    apply List.map_congr_left
    intro b hb
    rw [hbranch b hb witness hv,amplitude_norm]
    rfl

/-- Zero accumulator and shared scratch, with a canonical multiplicand. -/
def HornerInputValid (input acc : List Wire) (p : Nat) (c r t f : Wire) (s : BasisState) : Prop :=
  Clean acc s ∧ s c = false ∧ s r = false ∧ s t = false ∧ s f = false ∧
    boolWordToNat (wireValues input s) < p

private theorem clean_word_zero (ws : List Wire) (s : BasisState) (h : Clean ws s) :
    boolWordToNat (wireValues ws s) = 0 := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have hw := h w (by simp)
    have ht : Clean ws s := fun v hv => h v (by simp [hv])
    change boolWordToNat (s w :: wireValues ws s) = 0
    rw [boolWordToNat,hw,ih ht]
    rfl

private theorem horner_zero_valid (input acc : List Wire) (p : Nat) (c r t f : Wire) (hp : 0 < p) :
    HornerInputValid input acc p c r t f (fun _ => false) := by
  refine ⟨fun _ _ => rfl,rfl,rfl,rfl,rfl,?_⟩
  rw [clean_word_zero input _ (fun _ _ => rfl)]
  exact hp

/-- The literal Horner multiplier has one normalized expansion for all valid inputs. -/
theorem hornerMul_coherent (controls input : List Wire) (a : Wire) (rest : List Wire)
    (correction : List Bool) (p : Nat) (c r t f : Wire)
    (hlen : input.length = (a :: rest).length) (hk : (a :: rest).length = correction.length)
    (hnd : ([c,r,t,f] ++ controls ++ input ++ (a :: rest)).Nodup)
    (hp : p < 2 ^ (a :: rest).length) (hodd : p % 2 = 1)
    (hconstant : boolWordToNat correction = 2 ^ (a :: rest).length - p) :
    CoherentlyImplementsOn (hornerMul controls input (a :: rest) correction p c r t f)
      (Finsupp.lmapDomain ℂ ℂ (hornerMulIdealState controls input (a :: rest) correction p c f))
      (HornerInputValid input (a :: rest) p c r t f) := by
  apply coherent_branches _ _ _ (hornerMul_wellFormed controls input a rest correction p c r t f hlen hk hnd)
    (fun _ => false) (horner_zero_valid input (a :: rest) p c r t f (by omega))
  intro b hb s hs
  exact hornerMul_branch_correct controls input a rest correction p c r t f s hlen hk hnd
    hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.1 hp hodd hs.2.2.2.2.2
    (clean_word_zero _ _ hs.1) hconstant b hb

/-- Clear the output bank in the inverse's deterministic ideal, preserving its full frame. -/
def hornerClearOutput (acc : List Wire) (s : BasisState) : BasisState :=
  fun w => if w ∈ acc then false else s w

private theorem horner_clear_after_forward (controls input : List Wire) (a : Wire) (rest : List Wire)
    (correction : List Bool) (p : Nat) (c r t f : Wire) (s : BasisState)
    (hlen : input.length = (a :: rest).length) (hk : (a :: rest).length = correction.length)
    (hnd : ([c,r,t,f] ++ controls ++ input ++ (a :: rest)).Nodup)
    (hp : p < 2 ^ (a :: rest).length) (hodd : p % 2 = 1)
    (hconstant : boolWordToNat correction = 2 ^ (a :: rest).length - p)
    (hs : HornerInputValid input (a :: rest) p c r t f s) :
    hornerClearOutput (a :: rest) (hornerMulIdealState controls input (a :: rest) correction p c f s) = s := by
  have hframe := (hornerMulIdealState_correct controls input a rest correction p c r t f s hlen hk hnd
    hs.2.1 hs.2.2.2.2.1 hp hodd hs.2.2.2.2.2 (clean_word_zero _ _ hs.1) hconstant).2
  funext w
  by_cases hw : w ∈ a :: rest
  · simp [hornerClearOutput,hw,hs.1 w hw]
  · simp [hornerClearOutput,hw,hframe w hw]

/-- The literal inverse coherently clears the product on the actual forward image. -/
theorem hornerMulInverse_coherent (controls input : List Wire) (a : Wire) (rest : List Wire)
    (correction modulus : List Bool) (p : Nat) (c r t f : Wire)
    (hlen : input.length = (a :: rest).length) (hk : (a :: rest).length = correction.length)
    (hm : (a :: rest).length = modulus.length)
    (hnd : ([c,r,t,f] ++ controls ++ input ++ (a :: rest)).Nodup)
    (hp : p < 2 ^ (a :: rest).length) (hodd : p % 2 = 1)
    (hconstant : boolWordToNat correction = 2 ^ (a :: rest).length - p)
    (hmodulus : boolWordToNat modulus = p) :
    CoherentlyImplementsOn (hornerMulInverse controls input (a :: rest) modulus p c r t f)
      (Finsupp.lmapDomain ℂ ℂ (hornerClearOutput (a :: rest)))
      (fun state => ∃ s, HornerInputValid input (a :: rest) p c r t f s ∧
        state = hornerMulIdealState controls input (a :: rest) correction p c f s) := by
  apply coherent_branches _ _ _
    (hornerMulInverse_wellFormed controls input a rest modulus p c r t f hlen hm hnd)
    (hornerMulIdealState controls input (a :: rest) correction p c f (fun _ => false))
    ⟨_,horner_zero_valid input (a :: rest) p c r t f (by omega),rfl⟩
  intro b hb state hs
  obtain ⟨s,hs,rfl⟩ := hs
  rw [horner_clear_after_forward controls input a rest correction p c r t f s hlen hk hnd hp hodd hconstant hs]
  exact hornerMulInverse_after_forward controls input a rest correction modulus p c r t f s
    hlen hk hm hnd hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.1 hp hodd hs.2.2.2.2.2
    (clean_word_zero _ _ hs.1) hconstant hmodulus b hb

/-- The actual multiply/inverse pair is coherent identity, including the complete external frame. -/
theorem hornerMul_forward_inverse_coherent (controls input : List Wire) (a : Wire) (rest : List Wire)
    (correction modulus : List Bool) (p : Nat) (c r t f : Wire)
    (hlen : input.length = (a :: rest).length) (hk : (a :: rest).length = correction.length)
    (hm : (a :: rest).length = modulus.length)
    (hnd : ([c,r,t,f] ++ controls ++ input ++ (a :: rest)).Nodup)
    (hp : p < 2 ^ (a :: rest).length) (hodd : p % 2 = 1)
    (hconstant : boolWordToNat correction = 2 ^ (a :: rest).length - p)
    (hmodulus : boolWordToNat modulus = p) :
    CoherentlyImplementsOn ((hornerMul controls input (a :: rest) correction p c r t f).seq
      (hornerMulInverse controls input (a :: rest) modulus p c r t f))
      (Finsupp.lmapDomain ℂ ℂ (fun s : BasisState => s))
      (HornerInputValid input (a :: rest) p c r t f) := by
  have hf := hornerMul_coherent controls input a rest correction p c r t f hlen hk hnd hp hodd hconstant
  have hi := hornerMulInverse_coherent controls input a rest correction modulus p c r t f
    hlen hk hm hnd hp hodd hconstant hmodulus
  have hall := hf.seq hi (by
    intro s hs
    rw [lift_ket]
    exact supportedOn_ket _ _ ⟨s,hs,rfl⟩)
  apply hall.congrIdeal
  intro s hs
  simp only [LinearMap.comp_apply,lift_ket]
  exact congrArg ket (horner_clear_after_forward controls input a rest correction p c r t f s
    hlen hk hnd hp hodd hconstant hs)

end
end ShorECDLP.Paper2607_13816
