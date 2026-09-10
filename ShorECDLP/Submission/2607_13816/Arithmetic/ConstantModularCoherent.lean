import ShorECDLP.Submission.«2607_13816».Arithmetic.UncontrolledModular
import ShorECDLP.Submission.«2607_13816».Arithmetic.SquareCoherent

namespace ShorECDLP.Paper2607_13816
open Classical Quantum

/-- Canonical target and clean helper wires; all other wires are arbitrary. -/
def ConstantModularValid (target : List Wire) (p : Nat) (c r t f : Wire) (s : BasisState) : Prop :=
  s c=false ∧ s r=false ∧ s t=false ∧ s f=false ∧ boolWordToNat (wireValues target s)<p

private theorem constantModular_zero_valid (target : List Wire) (p : Nat) (c r t f : Wire)
    (hp : 0<p) : ConstantModularValid target p c r t f (fun _ => false) := by
  have hz (ws : List Wire) : boolWordToNat (wireValues ws (fun _ => false))=0 := by
    induction ws with
    | nil => rfl
    | cons w ws ih => simpa [wireValues,boolWordToNat] using ih
  exact ⟨rfl,rfl,rfl,rfl,by rw [hz]; exact hp⟩

/-- Every controlled source branch implements the same linear map with normalized weights. -/
theorem controlledConstantModularAdd_coherent (target dirty : List Wire) (constant correction : List Bool)
    (p : Nat) (q c r t f : Wire) (hk : target.length=constant.length) (hr : target.length=correction.length)
    (hd : target.length=dirty.length) (hn : 0<target.length)
    (hnd : ([q,c,r,t,f]++target++dirty).Nodup) (hp : 0<p) :
    CoherentlyImplementsOn (controlledConstantModularAdd target dirty constant correction p q c r t f)
      (Finsupp.lmapDomain ℂ ℂ (constantModularAddIdealState target constant correction p q f))
      (ConstantModularValid target p c r t f) := by
  apply coherent_history_branches _ _ _
    (controlledConstantModularAdd_wellFormed target dirty constant correction p q c r t f hk hr hd hn hnd)
    (fun _ => false) (constantModular_zero_valid target p c r t f hp)
  intro b hb s hs
  exact controlledConstantModularAdd_branch_correct target dirty constant correction p q c r t f s
    hk hr hd hn hnd hs.1 hs.2.1 hs.2.2.1 b hb

/-- Every unconditional source branch implements the same linear map with normalized weights. -/
theorem uncontrolledConstantModularAdd_coherent (target dirty : List Wire) (constant correction : List Bool)
    (p : Nat) (c r t f : Wire) (hk : target.length=constant.length) (hr : target.length=correction.length)
    (hd : target.length=dirty.length) (hn : 0<target.length)
    (hnd : ([c,r,t,f]++target++dirty).Nodup) (hp : 0<p) :
    CoherentlyImplementsOn (uncontrolledConstantModularAdd target dirty constant correction p c r t f)
      (Finsupp.lmapDomain ℂ ℂ (uncontrolledConstantModularAddIdealState target constant correction p f))
      (ConstantModularValid target p c r t f) := by
  apply coherent_history_branches _ _ _
    (uncontrolledConstantModularAdd_wellFormed target dirty constant correction p c r t f hk hr hd hn hnd)
    (fun _ => false) (constantModular_zero_valid target p c r t f hp)
  intro b hb s hs
  exact uncontrolledConstantModularAdd_branch_correct target dirty constant correction p c r t f s
    hk hr hd hn hnd hs.1 hs.2.1 hs.2.2.1 b hb

end ShorECDLP.Paper2607_13816
