import ShorECDLP.Submission.«2607_13816».Arithmetic.SquareInverse
import ShorECDLP.Submission.«2607_13816».Arithmetic.HornerCoherent
/-!
# Coherent source squaring and explicit inverse

The branch amplitudes depend only on transcript length. A clean zero-input
witness establishes their common normalization, so these contracts preserve
superpositions while composing the source square and its explicit inverse.
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
theorem coherent_history_branches (program : AdaptiveCircuit)
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

/-- Zero accumulator and shared scratch, with a canonical input. -/
def SquareInputValid (input acc : List Wire) (p : Nat) (copied c r t f : Wire) (s : BasisState) : Prop :=
  s copied=false ∧ HornerInputValid input acc p c r t f s

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

private theorem square_zero_valid (input acc : List Wire) (p : Nat) (copied c r t f : Wire) (hp : 0 < p) :
    SquareInputValid input acc p copied c r t f (fun _ => false) := by
  refine ⟨rfl,fun _ _ => rfl,rfl,rfl,rfl,rfl,?_⟩
  rw [clean_word_zero input _ (fun _ _ => rfl)]
  exact hp

/-- The literal source square has one normalized expansion for all valid inputs. -/
theorem squareLoop_coherent (controls input : List Wire) (a : Wire) (rest : List Wire)
    (correction : List Bool) (p : Nat) (copied c r t f : Wire)
    (hlen : input.length = (a :: rest).length) (hk : (a :: rest).length = correction.length)
    (hnd : ([copied,c,r,t,f] ++ input ++ (a :: rest)).Nodup)
    (hcontrols : ∀ bit ∈ controls, bit ∈ input)
    (hp : p < 2 ^ (a :: rest).length) (hodd : p % 2 = 1)
    (hconstant : boolWordToNat correction = 2 ^ (a :: rest).length - p) :
    CoherentlyImplementsOn (squareLoop controls input (a :: rest) correction p copied c r t f)
      (Finsupp.lmapDomain ℂ ℂ (squareLoopIdealState controls input (a :: rest) correction p copied c f))
      (SquareInputValid input (a :: rest) p copied c r t f) := by
  apply coherent_history_branches _ _ _ (squareLoop_wellFormed controls input a rest correction p copied c r t f hlen hk hnd hcontrols)
    (fun _ => false) (square_zero_valid input (a :: rest) p copied c r t f (by omega))
  intro b hb s hs
  exact squareLoop_branch_correct controls input a rest correction p copied c r t f s hlen hk hnd hcontrols
    hs.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.1 hs.2.2.2.2.2.1 hp hodd hs.2.2.2.2.2.2
    (clean_word_zero _ _ hs.2.1) hconstant b hb

private theorem square_clear_after_forward (controls input : List Wire) (a : Wire) (rest : List Wire)
    (correction : List Bool) (p : Nat) (copied c r t f : Wire) (s : BasisState)
    (hlen : input.length = (a :: rest).length) (hk : (a :: rest).length = correction.length)
    (hnd : ([copied,c,r,t,f] ++ input ++ (a :: rest)).Nodup)
    (hcontrols : ∀ bit ∈ controls, bit ∈ input)
    (hp : p < 2 ^ (a :: rest).length) (hodd : p % 2 = 1)
    (hconstant : boolWordToNat correction = 2 ^ (a :: rest).length - p)
    (hs : SquareInputValid input (a :: rest) p copied c r t f s) :
    hornerClearOutput (a :: rest) (squareLoopIdealState controls input (a :: rest) correction p copied c f s) = s := by
  have hframe := (squareLoopIdealState_correct controls input a rest correction p copied c r t f s hlen hk hnd hcontrols
    hs.1 hs.2.2.1 hs.2.2.2.2.2.1 hp hodd hs.2.2.2.2.2.2 (clean_word_zero _ _ hs.2.1) hconstant).2
  funext w
  by_cases hw : w ∈ a :: rest
  · simp [hornerClearOutput,hw,hs.2.1 w hw]
  · simp [hornerClearOutput,hw,hframe w hw]

/-- The literal inverse coherently clears the square on the actual forward image. -/
theorem squareLoopInverse_coherent (controls input : List Wire) (a : Wire) (rest : List Wire)
    (correction modulus : List Bool) (p : Nat) (copied c r t f : Wire)
    (hlen : input.length = (a :: rest).length) (hk : (a :: rest).length = correction.length)
    (hm : (a :: rest).length = modulus.length)
    (hnd : ([copied,c,r,t,f] ++ input ++ (a :: rest)).Nodup)
    (hcontrols : ∀ bit ∈ controls, bit ∈ input)
    (hp : p < 2 ^ (a :: rest).length) (hodd : p % 2 = 1)
    (hconstant : boolWordToNat correction = 2 ^ (a :: rest).length - p)
    (hmodulus : boolWordToNat modulus = p) :
    CoherentlyImplementsOn (squareLoopInverse controls input (a :: rest) modulus p copied c r t f)
      (Finsupp.lmapDomain ℂ ℂ (hornerClearOutput (a :: rest)))
      (fun state => ∃ s, SquareInputValid input (a :: rest) p copied c r t f s ∧
        state = squareLoopIdealState controls input (a :: rest) correction p copied c f s) := by
  apply coherent_history_branches _ _ _
    (squareLoopInverse_wellFormed controls input a rest modulus p copied c r t f hlen hm hnd hcontrols)
    (squareLoopIdealState controls input (a :: rest) correction p copied c f (fun _ => false))
    ⟨_,square_zero_valid input (a :: rest) p copied c r t f (by omega),rfl⟩
  intro b hb state hs
  obtain ⟨s,hs,rfl⟩ := hs
  rw [square_clear_after_forward controls input a rest correction p copied c r t f s hlen hk hnd hcontrols hp hodd hconstant hs]
  exact squareLoopInverse_after_forward controls input a rest correction modulus p copied c r t f s
    hlen hk hm hnd hcontrols hs.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.1 hs.2.2.2.2.2.1 hp hodd hs.2.2.2.2.2.2
    (clean_word_zero _ _ hs.2.1) hconstant hmodulus b hb

/-- The actual square/inverse pair is coherent identity, including the complete external frame. -/
theorem squareLoop_forward_inverse_coherent (controls input : List Wire) (a : Wire) (rest : List Wire)
    (correction modulus : List Bool) (p : Nat) (copied c r t f : Wire)
    (hlen : input.length = (a :: rest).length) (hk : (a :: rest).length = correction.length)
    (hm : (a :: rest).length = modulus.length)
    (hnd : ([copied,c,r,t,f] ++ input ++ (a :: rest)).Nodup)
    (hcontrols : ∀ bit ∈ controls, bit ∈ input)
    (hp : p < 2 ^ (a :: rest).length) (hodd : p % 2 = 1)
    (hconstant : boolWordToNat correction = 2 ^ (a :: rest).length - p)
    (hmodulus : boolWordToNat modulus = p) :
    CoherentlyImplementsOn ((squareLoop controls input (a :: rest) correction p copied c r t f).seq
      (squareLoopInverse controls input (a :: rest) modulus p copied c r t f))
      (Finsupp.lmapDomain ℂ ℂ (fun s : BasisState => s))
      (SquareInputValid input (a :: rest) p copied c r t f) := by
  have hf := squareLoop_coherent controls input a rest correction p copied c r t f hlen hk hnd hcontrols hp hodd hconstant
  have hi := squareLoopInverse_coherent controls input a rest correction modulus p copied c r t f
    hlen hk hm hnd hcontrols hp hodd hconstant hmodulus
  have hall := hf.seq hi (by
    intro s hs
    rw [lift_ket]
    exact supportedOn_ket _ _ ⟨s,hs,rfl⟩)
  apply hall.congrIdeal
  intro s hs
  simp only [LinearMap.comp_apply,lift_ket]
  exact congrArg ket (square_clear_after_forward controls input a rest correction p copied c r t f s
    hlen hk hnd hcontrols hp hodd hconstant hs)

end
end ShorECDLP.Paper2607_13816
