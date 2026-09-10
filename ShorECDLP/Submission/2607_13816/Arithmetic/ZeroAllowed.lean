import ShorECDLP.Submission.«2607_13816».Arithmetic.InPlace
import ShorECDLP.Submission.«2607_13816».EEA.TopBoundary
/-!
# Reversible zero-input extension of Figure 15

The paper arithmetic requires nonzero X. These wrappers detect zero into an
external clean flag, temporarily replace X=0 by X=1, execute the unchanged
Figure 15 operation, and restore X and the flag. They extend field operations;
they do not assert correctness of exceptional elliptic-curve point addition.
-/
namespace ShorECDLP.Paper2607_13816
open Classical Quantum

def nonzeroInputPrepare (a : Wire) (rest : List Wire) (flag : Wire) (scratch : List Wire) : Circuit :=
  computeEqConst (a::rest) 0 flag scratch ++ [.CX flag a]

def nonzeroInputPrepareState (a : Wire) (rest : List Wire) (flag : Wire) (s : BasisState) : BasisState :=
  let b := decide (boolWordToNat (wireValues (a::rest) s)=0)
  upd (upd s flag b) a (Bool.xor (s a) b)

theorem nonzeroInputPrepare_run (a : Wire) (rest : List Wire) (flag : Wire) (scratch : List Wire)
    (s : BasisState) (hl : EqConstLayout (a::rest) flag scratch) (hc : Clean scratch s)
    (hf : s flag=false) :
    Classical.run (nonzeroInputPrepare a rest flag scratch) s=nonzeroInputPrepareState a rest flag s := by
  have hneq : a≠flag := by intro h; subst a; simp [EqConstLayout,McxVChainLayout] at hl
  rw [nonzeroInputPrepare,Classical.run_append,run_computeEqConst _ _ _ _ _ hl hc]
  rw [registerMatches_eq_numeric _ _ _ (Nat.two_pow_pos _)]
  simp [Classical.run,Classical.applyGate,hf,nonzeroInputPrepareState,upd,hneq]

theorem nonzeroInputPrepareState_correct (a : Wire) (rest : List Wire) (flag : Wire)
    (s : BasisState) (hn : (a::rest).Nodup) (hf : flag ∉ a::rest) :
    boolWordToNat (wireValues (a::rest) (nonzeroInputPrepareState a rest flag s))=
      if boolWordToNat (wireValues (a::rest) s)=0 then 1 else boolWordToNat (wireValues (a::rest) s) := by
  have hrest : wireValues rest (nonzeroInputPrepareState a rest flag s)=wireValues rest s := by
    apply List.map_congr_left
    intro w hw
    have hwa : w≠a := by intro h; exact (List.nodup_cons.mp hn).1 (h ▸ hw)
    have hwf : w≠flag := by intro h; exact hf (by simp [←h,hw])
    simp [nonzeroInputPrepareState,upd,hwa,hwf]
  have he : (nonzeroInputPrepareState a rest flag s) a =
      Bool.xor (s a) (decide (boolWordToNat (wireValues (a::rest) s)=0)) := by
    simp only [nonzeroInputPrepareState,upd_same]
  by_cases hz : boolWordToNat (wireValues (a::rest) s)=0
  · have ha : s a=false := by
      have hh := hz
      simp only [wireValues,List.map_cons,boolWordToNat] at hh
      cases he : s a <;> simp_all
    have hr : boolWordToNat (wireValues rest s)=0 := by
      simpa [wireValues,boolWordToNat,ha] using hz
    rw [if_pos hz]
    change ((nonzeroInputPrepareState a rest flag s) a).toNat +
      2 * boolWordToNat (wireValues rest (nonzeroInputPrepareState a rest flag s))=1
    rw [he,hrest,hr]
    simp only [hz,decide_true,ha,Bool.false_xor,Bool.toNat_true,Nat.mul_zero,Nat.add_zero]
  · rw [if_neg hz]
    change ((nonzeroInputPrepareState a rest flag s) a).toNat +
      2 * boolWordToNat (wireValues rest (nonzeroInputPrepareState a rest flag s))=_
    rw [he,hrest]
    simp only [hz,decide_false,Bool.xor_false]
    rfl

def fig15ZeroPrepare : Circuit := nonzeroInputPrepare 263 (List.range' 264 255) 837 (List.range' 7 254)
def fig15ZeroPrepareState (s : BasisState) : BasisState :=
  nonzeroInputPrepareState 263 (List.range' 264 255) 837 s

def Secp256k1ZeroAllowedInputValid (s : BasisState) : Prop :=
  Clean (List.range' 0 263 ++ List.range' 519 61) s ∧ s 837=false ∧
  boolWordToNat (wireValues (List.range' 263 256) s)<ShorECDLP.p ∧
  boolWordToNat (wireValues (List.range' 580 256) s)<ShorECDLP.p

private theorem zeroPrepare_register : 263::List.range' 264 255=List.range' 263 256 := by decide +kernel
private theorem zeroPrepare_layout : EqConstLayout (263::List.range' 264 255) 837 (List.range' 7 254) := by
  unfold EqConstLayout McxVChainLayout
  decide +kernel

theorem fig15ZeroPrepare_run (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) :
    Classical.run fig15ZeroPrepare s=fig15ZeroPrepareState s := by
  apply nonzeroInputPrepare_run _ _ _ _ _ zeroPrepare_layout _ hs.2.1
  intro w hw
  apply hs.1 w
  simp at hw ⊢
  omega

theorem fig15ZeroPrepareState_ready (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) :
    Secp256k1InPlaceInputValid (fig15ZeroPrepareState s) := by
  have hword := nonzeroInputPrepareState_correct 263 (List.range' 264 255) 837 s
    (by decide +kernel) (by decide +kernel)
  change boolWordToNat (wireValues (263::List.range' 264 255) (fig15ZeroPrepareState s))=_ at hword
  rw [zeroPrepare_register] at hword
  have hf (w : Wire) (h1 : w≠263) (h2 : w≠837) : fig15ZeroPrepareState s w=s w := by
    simp [fig15ZeroPrepareState,nonzeroInputPrepareState,upd,h1,h2]
  have hp : 1<ShorECDLP.p := by decide +kernel
  have hx := hs.2.2.1
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  · intro w hw
    have h1 : w≠263 := by simp at hw; dsimp only [Wire] at *; omega
    have h2 : w≠837 := by simp at hw; dsimp only [Wire] at *; omega
    rw [hf w h1 h2]
    exact hs.1 w hw
  · rw [hword]
    split <;> omega
  · rw [hword]
    split <;> omega
  · have hy : wireValues (List.range' 580 256) (fig15ZeroPrepareState s)=wireValues (List.range' 580 256) s := by
      apply List.map_congr_left
      intro w hw
      apply hf <;> simp at hw <;> dsimp only [Wire] at * <;> omega
    rw [hy]
    exact hs.2.2.2

def nonzeroInputRestore (a : Wire) (rest : List Wire) (flag : Wire) (scratch : List Wire) : Circuit :=
  [.CX flag a] ++ computeEqConst (a::rest) 0 flag scratch

theorem nonzeroInputRestore_inverse (a : Wire) (rest : List Wire) (flag : Wire) (scratch : List Wire)
    (s : BasisState) (hl : EqConstLayout (a::rest) flag scratch) (hc : Clean scratch s) :
    Classical.run (nonzeroInputRestore a rest flag scratch)
      (Classical.run (nonzeroInputPrepare a rest flag scratch) s)=s := by
  have hneq : a≠flag := by intro h; subst a; simp [EqConstLayout,McxVChainLayout] at hl
  have hcx (t : BasisState) : Classical.run [.CX flag a] (Classical.run [.CX flag a] t)=t := by
    funext w
    by_cases hwa : w=a <;> simp [Classical.run,Classical.applyGate,upd,hneq.symm,hwa]
  rw [nonzeroInputRestore,nonzeroInputPrepare,Classical.run_append,Classical.run_append,hcx]
  exact run_computeEqConst_twice _ _ _ _ _ hl hc

def fig15ZeroRestore : Circuit := nonzeroInputRestore 263 (List.range' 264 255) 837 (List.range' 7 254)

def secp256k1ZeroAllowedDivision : AdaptiveCircuit :=
  ((AdaptiveCircuit.unitary fig15ZeroPrepare .done).seq secp256k1InPlaceDivision).seq (.unitary fig15ZeroRestore .done)

def secp256k1ZeroAllowedMultiplication : AdaptiveCircuit :=
  ((AdaptiveCircuit.unitary fig15ZeroPrepare .done).seq secp256k1InPlaceMultiplication).seq (.unitary fig15ZeroRestore .done)

def zeroAllowedDivisionOutputState (s : BasisState) : BasisState :=
  Classical.run fig15ZeroRestore (fig15DivisionOutputState (fig15ZeroPrepareState s))

def zeroAllowedMultiplicationOutputState (s : BasisState) : BasisState :=
  Classical.run fig15ZeroRestore (fig15MultiplicationOutputState (fig15ZeroPrepareState s))

private def zeroPrepareSupport : List Wire :=
  (263::List.range' 264 255) ++ 837::List.range' 7 254
private theorem zeroRestore_usesOnly : PaperCircuitUsesOnly zeroPrepareSupport fig15ZeroRestore := by
  apply PaperCircuitUsesOnly.append
  · intro g hg w hw
    simp only [List.mem_singleton] at hg
    subst g
    simp only [gateWires,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl <;> simp [zeroPrepareSupport]
  · exact computeEqConst_usesOnly _ _ _ _
private theorem zeroSupport_outside_data (w : Wire) (hw : w ∈ zeroPrepareSupport) :
    w ∉ List.range' 580 256 := by
  simp [zeroPrepareSupport] at hw ⊢
  dsimp only [Wire] at *
  omega

theorem fig15ZeroRestore_frame (s t : BasisState) (hs : Secp256k1ZeroAllowedInputValid s)
    (ht : ∀ w, w ∉ List.range' 580 256 → t w=fig15ZeroPrepareState s w) :
    Classical.run fig15ZeroRestore t=fun w => if w ∈ List.range' 580 256 then t w else s w := by
  have hi : Classical.run fig15ZeroRestore (fig15ZeroPrepareState s)=s := by
    rw [←fig15ZeroPrepare_run s hs]
    apply nonzeroInputRestore_inverse _ _ _ _ _ zeroPrepare_layout
    intro w hw
    apply hs.1 w
    simp at hw ⊢
    omega
  have hlocal := zeroRestore_usesOnly.run_congrOn t (fig15ZeroPrepareState s)
    (fun w hw => ht w (zeroSupport_outside_data w hw))
  funext w
  by_cases hy : w ∈ List.range' 580 256
  · rw [if_pos hy]
    exact zeroRestore_usesOnly.preservesOutside t (fun hw => zeroSupport_outside_data w hw hy)
  · rw [if_neg hy]
    by_cases hw : w ∈ zeroPrepareSupport
    · exact (hlocal w hw).trans (congrFun hi w)
    · rw [zeroRestore_usesOnly.preservesOutside t hw,ht w hy]
      have ha : w≠263 := by intro he; subst w; simp [zeroPrepareSupport] at hw
      have hf : w≠837 := by intro he; subst w; simp [zeroPrepareSupport] at hw
      simp [fig15ZeroPrepareState,nonzeroInputPrepareState,upd,ha,hf]
attribute [local irreducible] secp256k1InPlaceDivision secp256k1InPlaceMultiplication
  fig15DivisionOutputState fig15MultiplicationOutputState

theorem zeroAllowedDivisionOutputState_frame (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) :
    zeroAllowedDivisionOutputState s=fun w => if w ∈ List.range' 580 256 then
      fig15DivisionOutputState (fig15ZeroPrepareState s) w else s w := by
  apply fig15ZeroRestore_frame s _ hs
  intro w hw
  simp only [fig15DivisionOutputState_eq _ (fig15ZeroPrepareState_ready s hs),if_neg hw]

theorem zeroAllowedMultiplicationOutputState_frame (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) :
    zeroAllowedMultiplicationOutputState s=fun w => if w ∈ List.range' 580 256 then
      fig15MultiplicationOutputState (fig15ZeroPrepareState s) w else s w := by
  apply fig15ZeroRestore_frame s _ hs
  intro w hw
  simp only [fig15MultiplicationOutputState_eq _ (fig15ZeroPrepareState_ready s hs),if_neg hw]

private theorem zeroPrepare_data (s : BasisState) :
    wireValues (List.range' 580 256) (fig15ZeroPrepareState s)=wireValues (List.range' 580 256) s := by
  apply List.map_congr_left
  intro w hw
  have ha : w≠263 := by simp at hw; dsimp only [Wire] at *; omega
  have hf : w≠837 := by simp at hw; dsimp only [Wire] at *; omega
  simp [fig15ZeroPrepareState,nonzeroInputPrepareState,upd,ha,hf]
private theorem zeroPrepare_word (s : BasisState) :
    boolWordToNat (wireValues (List.range' 263 256) (fig15ZeroPrepareState s))=
      if boolWordToNat (wireValues (List.range' 263 256) s)=0 then 1
      else boolWordToNat (wireValues (List.range' 263 256) s) := by
  simpa only [zeroPrepare_register] using nonzeroInputPrepareState_correct 263 (List.range' 264 255) 837 s
    (by decide +kernel) (by decide +kernel)

theorem zeroAllowedDivisionOutputState_word (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) :
    boolWordToNat (wireValues (List.range' 580 256) (zeroAllowedDivisionOutputState s))=
      (boolWordToNat (wireValues (List.range' 580 256) s) * paperInverse ShorECDLP.p
        (if boolWordToNat (wireValues (List.range' 263 256) s)=0 then 1
         else boolWordToNat (wireValues (List.range' 263 256) s)))%ShorECDLP.p := by
  have he : wireValues (List.range' 580 256) (zeroAllowedDivisionOutputState s)=
      wireValues (List.range' 580 256) (fig15DivisionOutputState (fig15ZeroPrepareState s)) := by
    apply List.map_congr_left
    intro w hw
    simp only [zeroAllowedDivisionOutputState_frame s hs,if_pos hw]
  rw [he,fig15DivisionOutputState_word _ (fig15ZeroPrepareState_ready s hs),zeroPrepare_data,zeroPrepare_word]

theorem zeroAllowedMultiplicationOutputState_word (s : BasisState) (hs : Secp256k1ZeroAllowedInputValid s) :
    boolWordToNat (wireValues (List.range' 580 256) (zeroAllowedMultiplicationOutputState s))=
      (boolWordToNat (wireValues (List.range' 580 256) s) *
        (if boolWordToNat (wireValues (List.range' 263 256) s)=0 then 1
         else boolWordToNat (wireValues (List.range' 263 256) s)))%ShorECDLP.p := by
  have he : wireValues (List.range' 580 256) (zeroAllowedMultiplicationOutputState s)=
      wireValues (List.range' 580 256) (fig15MultiplicationOutputState (fig15ZeroPrepareState s)) := by
    apply List.map_congr_left
    intro w hw
    simp only [zeroAllowedMultiplicationOutputState_frame s hs,if_pos hw]
  rw [he,fig15MultiplicationOutputState_word _ (fig15ZeroPrepareState_ready s hs),zeroPrepare_data,zeroPrepare_word]
private theorem zeroCX_wellFormed : CircuitWellFormed ([.CX 837 263] : Circuit) := by
  intro g hg
  have he := List.mem_singleton.mp hg
  subst g
  change (837 : Wire)≠263
  decide +kernel

theorem fig15ZeroPrepare_wellFormed : CircuitWellFormed fig15ZeroPrepare := by
  rw [fig15ZeroPrepare,nonzeroInputPrepare,circuitWellFormed_append]
  exact ⟨computeEqConst_wellFormed _ _ _ _ zeroPrepare_layout,zeroCX_wellFormed⟩
theorem fig15ZeroRestore_wellFormed : CircuitWellFormed fig15ZeroRestore := by
  rw [fig15ZeroRestore,nonzeroInputRestore,circuitWellFormed_append]
  exact ⟨zeroCX_wellFormed,computeEqConst_wellFormed _ _ _ _ zeroPrepare_layout⟩
end ShorECDLP.Paper2607_13816
