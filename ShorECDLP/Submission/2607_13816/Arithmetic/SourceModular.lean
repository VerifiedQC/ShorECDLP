import ShorECDLP.Submission.«2607_13816».Arithmetic.SourceAdapters
import ShorECDLP.Submission.«2607_13816».Arithmetic.UncontrolledModular
import ShorECDLP.Submission.«2607_13816».Arithmetic.ModularNegate
import ShorECDLP.Submission.«2607_13816».Arithmetic.Halving

namespace ShorECDLP.Paper2607_13816
/-- Source-marked variable modular addition; reversible unitary stages carry no selected-correction marker. -/
def controlledModularAddSource (input acc : List Wire) (correction : List Bool) (p : Nat)
    (q c r t f : Wire) : CorrectionProgram :=
  .unitary [.ordinary (controlledAddCarry input acc q c f)]
    ((gidneyCompareGESource acc input p c r t f).seq
      ((controlledGidneyAddConstSource acc (input.take (acc.length-1)) correction f c r t).seq
        (.unitary [.ordinary (controlledCompareLT acc input q c f)] .done)))
def controlledModularSubSource (input acc : List Wire) (modulus : List Bool) (p : Nat)
    (q c r t f : Wire) : CorrectionProgram :=
  .unitary [.ordinary (controlledCompareLT acc input q c f)]
    ((controlledGidneyAddConstSource acc (input.take (acc.length-1)) modulus f c r t).seq
      ((gidneyCompareGESource acc input p c r t f).seq
        (.unitary [.ordinary (controlledSubCarry input acc q c f)] .done)))
private theorem sourceOrdinary_erase (g : Circuit) (next : CorrectionProgram) :
    (CorrectionProgram.unitary [.ordinary g] next).erase=Quantum.AdaptiveCircuit.unitary g next.erase := by
  simp [CorrectionProgram.erase,correctionBlockErase,CorrectionFragment.erase]
private theorem sourceOrdinary_events (g : Circuit) (next : CorrectionProgram) :
    (CorrectionProgram.unitary [.ordinary g] next).events=next.events := by
  simp [CorrectionProgram.events,correctionBlockEvents,CorrectionFragment.events]
theorem controlledModularAddSource_erase (input acc : List Wire) (correction : List Bool) (p : Nat)
    (q c r t f : Wire) :
    (controlledModularAddSource input acc correction p q c r t f).erase=
      controlledModularAdd input acc correction p q c r t f := by
  simp only [controlledModularAddSource,controlledModularAdd,sourceOrdinary_erase,
    CorrectionProgram.erase_seq,gidneyCompareGESource_erase,controlledGidneyAddConstSource_erase,CorrectionProgram.erase,correctionBlockErase,CorrectionFragment.erase,List.flatMap_cons,List.flatMap_nil,List.append_nil]
theorem controlledModularSubSource_erase (input acc : List Wire) (modulus : List Bool) (p : Nat)
    (q c r t f : Wire) :
    (controlledModularSubSource input acc modulus p q c r t f).erase=
      controlledModularSub input acc modulus p q c r t f := by
  simp only [controlledModularSubSource,controlledModularSub,sourceOrdinary_erase,
    CorrectionProgram.erase_seq,gidneyCompareGESource_erase,controlledGidneyAddConstSource_erase,CorrectionProgram.erase,correctionBlockErase,CorrectionFragment.erase,List.flatMap_cons,List.flatMap_nil,List.append_nil]
theorem controlledModularAddSource_events (input acc : List Wire) (correction : List Bool) (p : Nat)
    (q c r t f : Wire) (hi : input.length=acc.length) (hn : 0 < acc.length) (hk : correction.length=acc.length) :
    (controlledModularAddSource input acc correction p q c r t f).events=
      (if p=0 ∨ 2^acc.length≤p then 0 else 2*acc.length)+
        (if correction.all (fun k => !k) then 0 else 2*(acc.length-1)) := by
  simp only [controlledModularAddSource,sourceOrdinary_events,CorrectionProgram.events_seq,
    gidneyCompareGESource_events _ _ _ _ _ _ _ hi,
    controlledGidneyAddConstSource_events acc (input.take (acc.length-1)) correction f c r t hn (by simp [List.length_take, hi]) hk,CorrectionProgram.events,correctionBlockEvents,CorrectionFragment.events,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
theorem controlledModularSubSource_events (input acc : List Wire) (modulus : List Bool) (p : Nat)
    (q c r t f : Wire) (hi : input.length=acc.length) (hn : 0 < acc.length) (hk : modulus.length=acc.length) :
    (controlledModularSubSource input acc modulus p q c r t f).events=
      (if modulus.all (fun k => !k) then 0 else 2*(acc.length-1))+
        (if p=0 ∨ 2^acc.length≤p then 0 else 2*acc.length) := by
  simp only [controlledModularSubSource,sourceOrdinary_events,CorrectionProgram.events_seq,
    gidneyCompareGESource_events _ _ _ _ _ _ _ hi,
    controlledGidneyAddConstSource_events acc (input.take (acc.length-1)) modulus f c r t hn (by simp [List.length_take, hi]) hk,CorrectionProgram.events,correctionBlockEvents,CorrectionFragment.events,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]

def controlledConstantModularAddSource (target dirty : List Wire) (constant correction : List Bool)
    (p : Nat) (q c r t f : Wire) : CorrectionProgram :=
  (controlledGidneyAddConstSource target (dirty.take (target.length-1)) constant q c r t).seq
    ((controlledGidneyCompareLTSource target dirty (boolWordToNat constant) q c r t f).seq
      ((gidneyCompareGESource target dirty p c r t f).seq
        ((controlledGidneyAddConstSource target (dirty.take (target.length-1)) correction f c r t).seq
          (controlledGidneyCompareLTSource target dirty (boolWordToNat constant) q c r t f))))
theorem controlledConstantModularAddSource_erase (target dirty : List Wire) (constant correction : List Bool)
    (p : Nat) (q c r t f : Wire) :
    (controlledConstantModularAddSource target dirty constant correction p q c r t f).erase=controlledConstantModularAdd target dirty constant correction p q c r t f := by
  simp only [controlledConstantModularAddSource,controlledConstantModularAdd,CorrectionProgram.erase_seq,controlledGidneyAddConstSource_erase,controlledGidneyCompareLTSource_erase,gidneyCompareGESource_erase]

def uncontrolledConstantModularAddSource (target dirty : List Wire) (constant correction : List Bool)
    (p : Nat) (c r t f : Wire) : CorrectionProgram :=
  (gidneyAddConstSource target (dirty.take (target.length-1)) constant c r t).seq
    ((gidneyCompareLTSource target dirty (boolWordToNat constant) c r t f).seq
      ((gidneyCompareGESource target dirty p c r t f).seq
        ((controlledGidneyAddConstSource target (dirty.take (target.length-1)) correction f c r t).seq
          (gidneyCompareLTSource target dirty (boolWordToNat constant) c r t f))))
theorem uncontrolledConstantModularAddSource_erase (target dirty : List Wire) (constant correction : List Bool)
    (p : Nat) (c r t f : Wire) :
    (uncontrolledConstantModularAddSource target dirty constant correction p c r t f).erase=uncontrolledConstantModularAdd target dirty constant correction p c r t f := by
  simp only [uncontrolledConstantModularAddSource,uncontrolledConstantModularAdd,CorrectionProgram.erase_seq,controlledGidneyAddConstSource_erase,gidneyAddConstSource_erase,gidneyCompareLTSource_erase,gidneyCompareGESource_erase]

def controlledModularNegateSource (target dirty : List Wire) (modulus : List Bool)
    (q c r t f : Wire) : CorrectionProgram :=
  (controlledGidneyCompareGESource target dirty 1 q c r t f).seq
    (.unitary [.ordinary (controlledComplement target q)]
      ((controlledGidneyAddConstSource target (dirty.take (target.length-1))
        ((List.range target.length).map (Nat.testBit 1)) q c r t).seq
        ((controlledGidneyAddConstSource target (dirty.take (target.length-1)) modulus f c r t).seq
          (controlledGidneyCompareGESource target dirty 1 q c r t f))))
theorem controlledModularNegateSource_erase (target dirty : List Wire) (modulus : List Bool)
    (q c r t f : Wire) :
    (controlledModularNegateSource target dirty modulus q c r t f).erase=controlledModularNegate target dirty modulus q c r t f := by
  simp only [controlledModularNegateSource,controlledModularNegate,CorrectionProgram.erase_seq,controlledGidneyAddConstSource_erase,controlledGidneyCompareGESource_erase,CorrectionProgram.erase,correctionBlockErase,CorrectionFragment.erase,List.flatMap_cons,List.flatMap_nil,List.append_nil]

def modularDoubleSource (acc dirty : List Wire) (correction : List Bool) (p : Nat) (c r t f : Wire) : CorrectionProgram :=
  match acc with
  | [] => .done
  | a :: rest => .unitary [.ordinary (doublingShift (a :: rest) f)]
      ((gidneyCompareGESource (a :: rest) dirty p c r t f).seq
        ((controlledGidneyAddConstSource (a :: rest) (dirty.take rest.length) correction f c r t).seq
          (.unitary [.ordinary [.CX a f]] .done)))
theorem modularDoubleSource_erase (acc dirty : List Wire) (correction : List Bool) (p : Nat) (c r t f : Wire) :
    (modularDoubleSource acc dirty correction p c r t f).erase=modularDouble acc dirty correction p c r t f := by
  cases acc <;> simp only [modularDoubleSource,modularDouble,CorrectionProgram.erase_seq,controlledGidneyAddConstSource_erase,gidneyCompareGESource_erase,CorrectionProgram.erase,correctionBlockErase,CorrectionFragment.erase,List.flatMap_cons,List.flatMap_nil,List.append_nil]

def modularHalveSource (acc dirty : List Wire) (modulus : List Bool) (p : Nat)
    (c r t f : Wire) : CorrectionProgram :=
  match acc with
  | [] => .done
  | a :: rest => .unitary [.ordinary [.CX a f]]
      ((controlledGidneyAddConstSource (a :: rest) (dirty.take rest.length) modulus f c r t).seq
        ((gidneyCompareGESource (a :: rest) dirty p c r t f).seq
          (.unitary [.ordinary (doublingShift (a :: rest) f).adjoint] .done)))
theorem modularHalveSource_erase (acc dirty : List Wire) (modulus : List Bool) (p : Nat)
    (c r t f : Wire) :
    (modularHalveSource acc dirty modulus p c r t f).erase=modularHalve acc dirty modulus p c r t f := by
  cases acc <;> simp only [modularHalveSource,modularHalve,CorrectionProgram.erase_seq,controlledGidneyAddConstSource_erase,gidneyCompareGESource_erase,CorrectionProgram.erase,correctionBlockErase,CorrectionFragment.erase,List.flatMap_cons,List.flatMap_nil,List.append_nil]

theorem controlledConstantModularAddSource_events (target dirty : List Wire) (constant correction : List Bool)
    (p : Nat) (q c r t f : Wire) (hn : 0 < target.length) (hd : dirty.length=target.length)
    (hk : constant.length=target.length) (hr : correction.length=target.length) :
    (controlledConstantModularAddSource target dirty constant correction p q c r t f).events=
      (if constant.all (fun k => !k) then 0 else 2*(target.length-1))+
        ((if boolWordToNat constant=0 ∨ 2^target.length≤boolWordToNat constant then 0 else 2*target.length)+
          ((if p=0 ∨ 2^target.length≤p then 0 else 2*target.length)+
            ((if correction.all (fun k => !k) then 0 else 2*(target.length-1))+
              (if boolWordToNat constant=0 ∨ 2^target.length≤boolWordToNat constant then 0 else 2*target.length)))) := by
  have hshort : (dirty.take (target.length-1)).length=target.length-1 := by simp [hd]
  simp only [controlledConstantModularAddSource,CorrectionProgram.events_seq,
    controlledGidneyAddConstSource_events target (dirty.take (target.length-1)) constant q c r t hn hshort hk,
    controlledGidneyCompareLTSource_events target dirty (boolWordToNat constant) q c r t f hd,
    gidneyCompareGESource_events target dirty p c r t f hd,
    controlledGidneyAddConstSource_events target (dirty.take (target.length-1)) correction f c r t hn hshort hr]

theorem uncontrolledConstantModularAddSource_events (target dirty : List Wire) (constant correction : List Bool)
    (p : Nat) (c r t f : Wire) (hn : 0 < target.length) (hd : dirty.length=target.length)
    (hk : constant.length=target.length) (hr : correction.length=target.length) :
    (uncontrolledConstantModularAddSource target dirty constant correction p c r t f).events=
      (if constant.all (fun k => !k) then 0 else 2*(target.length-1))+
        ((if boolWordToNat constant=0 ∨ 2^target.length≤boolWordToNat constant then 0 else 2*target.length)+
          ((if p=0 ∨ 2^target.length≤p then 0 else 2*target.length)+
            ((if correction.all (fun k => !k) then 0 else 2*(target.length-1))+
              (if boolWordToNat constant=0 ∨ 2^target.length≤boolWordToNat constant then 0 else 2*target.length)))) := by
  have hshort : (dirty.take (target.length-1)).length=target.length-1 := by simp [hd]
  simp only [uncontrolledConstantModularAddSource,CorrectionProgram.events_seq,
    gidneyAddConstSource_events target (dirty.take (target.length-1)) constant c r t hn hshort hk,
    gidneyCompareLTSource_events target dirty (boolWordToNat constant) c r t f hd,
    gidneyCompareGESource_events target dirty p c r t f hd,
    controlledGidneyAddConstSource_events target (dirty.take (target.length-1)) correction f c r t hn hshort hr]

theorem modularDoubleSource_events (a : Wire) (rest dirty : List Wire) (correction : List Bool)
    (p : Nat) (c r t f : Wire) (hd : dirty.length=(a::rest).length) (hk : correction.length=(a::rest).length) :
    (modularDoubleSource (a::rest) dirty correction p c r t f).events=(if p=0 ∨ 2^(a::rest).length≤p then 0 else 2*(a::rest).length)+(if correction.all (fun k => !k) then 0 else 2*rest.length) := by
  have hshort : (dirty.take rest.length).length=(a::rest).length-1 := by simp [hd]
  have ha := controlledGidneyAddConstSource_events (a::rest) (dirty.take rest.length) correction f c r t (by simp) hshort hk
  simp only [List.length_cons,Nat.add_sub_cancel] at ha
  simp only [modularDoubleSource,CorrectionProgram.events_seq,sourceOrdinary_events,
    gidneyCompareGESource_events (a::rest) dirty p c r t f hd,ha,
    CorrectionProgram.events,correctionBlockEvents,CorrectionFragment.events,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]

theorem modularHalveSource_events (a : Wire) (rest dirty : List Wire) (modulus : List Bool)
    (p : Nat) (c r t f : Wire) (hd : dirty.length=(a::rest).length) (hk : modulus.length=(a::rest).length) :
    (modularHalveSource (a::rest) dirty modulus p c r t f).events=(if modulus.all (fun k => !k) then 0 else 2*rest.length)+(if p=0 ∨ 2^(a::rest).length≤p then 0 else 2*(a::rest).length) := by
  have hshort : (dirty.take rest.length).length=(a::rest).length-1 := by simp [hd]
  have ha := controlledGidneyAddConstSource_events (a::rest) (dirty.take rest.length) modulus f c r t (by simp) hshort hk
  simp only [List.length_cons,Nat.add_sub_cancel] at ha
  simp only [modularHalveSource,CorrectionProgram.events_seq,sourceOrdinary_events,
    gidneyCompareGESource_events (a::rest) dirty p c r t f hd,ha,
    CorrectionProgram.events,correctionBlockEvents,CorrectionFragment.events,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
theorem controlledModularNegateSource_events (target dirty : List Wire) (modulus : List Bool)
    (q c r t f : Wire) (hn : 0 < target.length) (hd : dirty.length=target.length)
    (hm : modulus.length=target.length) :
    (controlledModularNegateSource target dirty modulus q c r t f).events=
      2*target.length + (2*(target.length-1) +
        ((if modulus.all (fun k => !k) then 0 else 2*(target.length-1))+2*target.length)) := by
  have hshort : (dirty.take (target.length-1)).length=target.length-1 := by simp [hd]
  have hone : ((List.range target.length).map (Nat.testBit 1)).all (fun k => !k)=false := by
    cases hh : target.length with
    | zero => omega
    | succ n =>
      rw [List.range_succ_eq_map]
      simp
  have hp : ¬(1=0 ∨ 2^target.length≤1) := by
    have hh : 1 < 2^target.length := Nat.one_lt_two_pow hn.ne'
    omega
  simp only [controlledModularNegateSource,CorrectionProgram.events_seq,sourceOrdinary_events,
    controlledGidneyCompareGESource_events target dirty 1 q c r t f hd,
    controlledGidneyAddConstSource_events target (dirty.take (target.length-1))
      ((List.range target.length).map (Nat.testBit 1)) q c r t hn hshort (by simp),
    controlledGidneyAddConstSource_events target (dirty.take (target.length-1)) modulus f c r t hn hshort hm,
    hp,if_false,hone,Bool.false_eq_true]
end ShorECDLP.Paper2607_13816
