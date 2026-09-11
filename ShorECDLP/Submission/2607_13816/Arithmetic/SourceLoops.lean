import ShorECDLP.Submission.«2607_13816».Arithmetic.SourceModular
import ShorECDLP.Submission.«2607_13816».Arithmetic.SquareInverse

namespace ShorECDLP.Paper2607_13816
def squareAddSource (input acc : List Wire) (correction : List Bool) (p : Nat)
    (q copied c r t f : Wire) : CorrectionProgram :=
  .unitary [.ordinary [.CX q copied]] ((controlledModularAddSource input acc correction p copied c r t f).seq
    (.unitary [.ordinary [.CX q copied]] .done))
theorem squareAddSource_erase (input acc : List Wire) (correction : List Bool) (p : Nat)
    (q copied c r t f : Wire) :
    (squareAddSource input acc correction p q copied c r t f).erase=squareAdd input acc correction p q copied c r t f := by
  simp only [squareAddSource,squareAdd,CorrectionProgram.erase_seq,controlledModularAddSource_erase,CorrectionProgram.erase,correctionBlockErase,CorrectionFragment.erase,List.flatMap_cons,List.flatMap_nil,List.append_nil]
def squareSubSource (input acc : List Wire) (modulus : List Bool) (p : Nat)
    (bit copied c r t f : Wire) : CorrectionProgram :=
  .unitary [.ordinary [.CX bit copied]] ((controlledModularSubSource input acc modulus p copied c r t f).seq
    (.unitary [.ordinary [.CX bit copied]] .done))
theorem squareSubSource_erase (input acc : List Wire) (modulus : List Bool) (p : Nat)
    (bit copied c r t f : Wire) :
    (squareSubSource input acc modulus p bit copied c r t f).erase=squareSub input acc modulus p bit copied c r t f := by
  simp only [squareSubSource,squareSub,CorrectionProgram.erase_seq,controlledModularSubSource_erase,CorrectionProgram.erase,correctionBlockErase,CorrectionFragment.erase,List.flatMap_cons,List.flatMap_nil,List.append_nil]
def hornerMulSource (controls input acc : List Wire) (correction : List Bool) (p : Nat)
    (c r t f : Wire) : CorrectionProgram :=
  match controls with
  | [] => .done
  | q :: qs => (hornerMulSource qs input acc correction p c r t f).seq
      (if qs = [] then controlledModularAddSource input acc correction p q c r t f else
        (modularDoubleSource acc input correction p f r t c).seq
          (controlledModularAddSource input acc correction p q c r t f))
theorem hornerMulSource_erase (controls input acc : List Wire) (correction : List Bool) (p : Nat)
    (c r t f : Wire) :
    (hornerMulSource controls input acc correction p c r t f).erase=hornerMul controls input acc correction p c r t f := by
  induction controls with
  | nil => rfl
  | cons bit bits ih =>
    by_cases h : bits=[] <;>
      simp [hornerMulSource,hornerMul,CorrectionProgram.erase_seq,controlledModularAddSource_erase,modularDoubleSource_erase,ih,h,CorrectionProgram.erase]

def hornerMulInverseSource (controls input acc : List Wire) (modulus : List Bool) (p : Nat)
    (c r t f : Wire) : CorrectionProgram :=
  match controls with
  | [] => .done
  | q :: qs => (controlledModularSubSource input acc modulus p q c r t f).seq
      (if qs = [] then .done else
        (modularHalveSource acc input modulus p f r t c).seq
          (hornerMulInverseSource qs input acc modulus p c r t f))
theorem hornerMulInverseSource_erase (controls input acc : List Wire) (modulus : List Bool) (p : Nat)
    (c r t f : Wire) :
    (hornerMulInverseSource controls input acc modulus p c r t f).erase=hornerMulInverse controls input acc modulus p c r t f := by
  induction controls with
  | nil => rfl
  | cons bit bits ih =>
    by_cases h : bits=[] <;>
      simp [hornerMulInverseSource,hornerMulInverse,CorrectionProgram.erase_seq,controlledModularSubSource_erase,modularHalveSource_erase,ih,h,CorrectionProgram.erase]

def squareLoopSource (controls input acc : List Wire) (correction : List Bool) (p : Nat)
    (copied c r t f : Wire) : CorrectionProgram :=
  match controls with
  | [] => .done
  | q :: qs => (squareLoopSource qs input acc correction p copied c r t f).seq
      (if qs = [] then squareAddSource input acc correction p q copied c r t f else
        (modularDoubleSource acc input correction p f r t c).seq
          (squareAddSource input acc correction p q copied c r t f))
theorem squareLoopSource_erase (controls input acc : List Wire) (correction : List Bool) (p : Nat)
    (copied c r t f : Wire) :
    (squareLoopSource controls input acc correction p copied c r t f).erase=squareLoop controls input acc correction p copied c r t f := by
  induction controls with
  | nil => rfl
  | cons bit bits ih =>
    by_cases h : bits=[] <;>
      simp [squareLoopSource,squareLoop,CorrectionProgram.erase_seq,squareAddSource_erase,modularDoubleSource_erase,ih,h,CorrectionProgram.erase]

def squareLoopInverseSource (controls input acc : List Wire) (modulus : List Bool) (p : Nat)
    (copied c r t f : Wire) : CorrectionProgram :=
  match controls with
  | [] => .done
  | bit::bits => (squareSubSource input acc modulus p bit copied c r t f).seq
      (if bits=[] then .done else (modularHalveSource acc input modulus p f r t c).seq
        (squareLoopInverseSource bits input acc modulus p copied c r t f))
theorem squareLoopInverseSource_erase (controls input acc : List Wire) (modulus : List Bool) (p : Nat)
    (copied c r t f : Wire) :
    (squareLoopInverseSource controls input acc modulus p copied c r t f).erase=squareLoopInverse controls input acc modulus p copied c r t f := by
  induction controls with
  | nil => rfl
  | cons bit bits ih =>
    by_cases h : bits=[] <;>
      simp [squareLoopInverseSource,squareLoopInverse,CorrectionProgram.erase_seq,squareSubSource_erase,modularHalveSource_erase,ih,h,CorrectionProgram.erase]
private theorem squareAddSource_events (input acc : List Wire) (constant : List Bool) (p : Nat)
    (q copied c r t f : Wire) :
    (squareAddSource input acc constant p q copied c r t f).events=
      (controlledModularAddSource input acc constant p copied c r t f).events := by
  simp [squareAddSource,CorrectionProgram.events_seq,CorrectionProgram.events,correctionBlockEvents,CorrectionFragment.events]
private theorem squareSubSource_events (input acc : List Wire) (constant : List Bool) (p : Nat)
    (q copied c r t f : Wire) :
    (squareSubSource input acc constant p q copied c r t f).events=
      (controlledModularSubSource input acc constant p copied c r t f).events := by
  simp [squareSubSource,CorrectionProgram.events_seq,CorrectionProgram.events,correctionBlockEvents,CorrectionFragment.events]
theorem hornerMulSource_events (controls input : List Wire) (a : Wire) (rest : List Wire)
    (constant : List Bool) (p : Nat) (c r t f : Wire)
    (hi : input.length=(a::rest).length) (hk : constant.length=(a::rest).length) :
    (hornerMulSource controls input (a::rest) constant p c r t f).events=
      (controls.length+(controls.length-1))*((if p=0 ∨ 2^(a::rest).length≤p then 0 else 2*(a::rest).length)+(if constant.all (fun k => !k) then 0 else 2*rest.length)) := by
  have hadd (q : Wire) := controlledModularAddSource_events input (a::rest) constant p q c r t f hi (by simp) hk
  simp only [List.length_cons,Nat.add_sub_cancel] at hadd
  have hshift := modularDoubleSource_events a rest input constant p f r t c hi hk
  induction controls with
  | nil => simp [hornerMulSource,CorrectionProgram.events]
  | cons q qs ih =>
    cases qs with
    | nil => simp [hornerMulSource,CorrectionProgram.events_seq,CorrectionProgram.events,hadd]
    | cons bit bits =>
      simp only [hornerMulSource,CorrectionProgram.events_seq,List.cons_ne_nil,if_false,hadd,hshift] at *
      simp only [List.length_cons,Nat.add_sub_cancel] at *
      rw [ih]
      ring
theorem hornerMulInverseSource_events (controls input : List Wire) (a : Wire) (rest : List Wire)
    (constant : List Bool) (p : Nat) (c r t f : Wire)
    (hi : input.length=(a::rest).length) (hk : constant.length=(a::rest).length) :
    (hornerMulInverseSource controls input (a::rest) constant p c r t f).events=
      (controls.length+(controls.length-1))*((if constant.all (fun k => !k) then 0 else 2*rest.length)+(if p=0 ∨ 2^(a::rest).length≤p then 0 else 2*(a::rest).length)) := by
  have hadd (q : Wire) := controlledModularSubSource_events input (a::rest) constant p q c r t f hi (by simp) hk
  simp only [List.length_cons,Nat.add_sub_cancel] at hadd
  have hshift := modularHalveSource_events a rest input constant p f r t c hi hk
  induction controls with
  | nil => simp [hornerMulInverseSource,CorrectionProgram.events]
  | cons q qs ih =>
    cases qs with
    | nil => simp [hornerMulInverseSource,CorrectionProgram.events_seq,CorrectionProgram.events,hadd]
    | cons bit bits =>
      simp only [hornerMulInverseSource,CorrectionProgram.events_seq,List.cons_ne_nil,if_false,hadd,hshift] at *
      simp only [List.length_cons,Nat.add_sub_cancel] at *
      rw [ih]
      ring
theorem squareLoopSource_events (controls input : List Wire) (a : Wire) (rest : List Wire)
    (constant : List Bool) (p : Nat) (copied c r t f : Wire)
    (hi : input.length=(a::rest).length) (hk : constant.length=(a::rest).length) :
    (squareLoopSource controls input (a::rest) constant p copied c r t f).events=
      (controls.length+(controls.length-1))*((if p=0 ∨ 2^(a::rest).length≤p then 0 else 2*(a::rest).length)+(if constant.all (fun k => !k) then 0 else 2*rest.length)) := by
  have hadd (q : Wire) := controlledModularAddSource_events input (a::rest) constant p q c r t f hi (by simp) hk
  simp only [List.length_cons,Nat.add_sub_cancel] at hadd
  have hshift := modularDoubleSource_events a rest input constant p f r t c hi hk
  induction controls with
  | nil => simp [squareLoopSource,CorrectionProgram.events]
  | cons q qs ih =>
    cases qs with
    | nil => simp [squareLoopSource,CorrectionProgram.events_seq,CorrectionProgram.events,squareAddSource_events,hadd]
    | cons bit bits =>
      simp only [squareLoopSource,CorrectionProgram.events_seq,List.cons_ne_nil,if_false,squareAddSource_events,hadd,hshift] at *
      simp only [List.length_cons,Nat.add_sub_cancel] at *
      rw [ih]
      ring
theorem squareLoopInverseSource_events (controls input : List Wire) (a : Wire) (rest : List Wire)
    (constant : List Bool) (p : Nat) (copied c r t f : Wire)
    (hi : input.length=(a::rest).length) (hk : constant.length=(a::rest).length) :
    (squareLoopInverseSource controls input (a::rest) constant p copied c r t f).events=
      (controls.length+(controls.length-1))*((if constant.all (fun k => !k) then 0 else 2*rest.length)+(if p=0 ∨ 2^(a::rest).length≤p then 0 else 2*(a::rest).length)) := by
  have hadd (q : Wire) := controlledModularSubSource_events input (a::rest) constant p q c r t f hi (by simp) hk
  simp only [List.length_cons,Nat.add_sub_cancel] at hadd
  have hshift := modularHalveSource_events a rest input constant p f r t c hi hk
  induction controls with
  | nil => simp [squareLoopInverseSource,CorrectionProgram.events]
  | cons q qs ih =>
    cases qs with
    | nil => simp [squareLoopInverseSource,CorrectionProgram.events_seq,CorrectionProgram.events,squareSubSource_events,hadd]
    | cons bit bits =>
      simp only [squareLoopInverseSource,CorrectionProgram.events_seq,List.cons_ne_nil,if_false,squareSubSource_events,hadd,hshift] at *
      simp only [List.length_cons,Nat.add_sub_cancel] at *
      rw [ih]
      ring
private theorem sourceReduction_nonzero : secp256k1ReductionConstantBits.all (fun k => !k)=false := by decide +kernel
private theorem sourceModulus_nonzero : secp256k1ModulusBits.all (fun k => !k)=false := by decide +kernel
private theorem sourceProduction_threshold : ¬((2^256-(2^32+977):Nat)=0 ∨ 2^256≤2^256-(2^32+977)) := by decide +kernel
def secp256k1HornerMulSource : CorrectionProgram :=
  hornerMulSource (List.range' 516 256) (List.range' 260 256) (List.range' 4 256)
    secp256k1ReductionConstantBits (2 ^ 256 - (2 ^ 32 + 977)) 1 2 3 0
/-- One literal production circuit and its exact worst-case selected-correction events. -/
theorem secp256k1HornerMulSource_certificate :
    secp256k1HornerMulSource.erase=secp256k1HornerMul ∧ secp256k1HornerMulSource.events=522242 := by
  constructor
  · exact hornerMulSource_erase _ _ _ _ _ _ _ _ _
  · have h := hornerMulSource_events (List.range' 516 256) (List.range' 260 256) 4 (List.range' 5 255)
      secp256k1ReductionConstantBits (2^256-(2^32+977)) 1 2 3 0 (by simp) (by decide +kernel)
    change secp256k1HornerMulSource.events=_ at h
    simpa only [List.length_range',List.length_cons,sourceProduction_threshold,if_false,sourceReduction_nonzero,Bool.false_eq_true] using h
def secp256k1HornerMulInverseSource : CorrectionProgram :=
  hornerMulInverseSource (List.range' 516 256) (List.range' 260 256) (List.range' 4 256)
    secp256k1ModulusBits (2 ^ 256 - (2 ^ 32 + 977)) 1 2 3 0
/-- One literal production circuit and its exact worst-case selected-correction events. -/
theorem secp256k1HornerMulInverseSource_certificate :
    secp256k1HornerMulInverseSource.erase=secp256k1HornerMulInverse ∧ secp256k1HornerMulInverseSource.events=522242 := by
  constructor
  · exact hornerMulInverseSource_erase _ _ _ _ _ _ _ _ _
  · have h := hornerMulInverseSource_events (List.range' 516 256) (List.range' 260 256) 4 (List.range' 5 255)
      secp256k1ModulusBits (2^256-(2^32+977)) 1 2 3 0 (by simp) (by decide +kernel)
    change secp256k1HornerMulInverseSource.events=_ at h
    simpa only [List.length_range',List.length_cons,sourceProduction_threshold,if_false,sourceModulus_nonzero,Bool.false_eq_true] using h
def secp256k1SquareSource : CorrectionProgram :=
  squareLoopSource (List.range' 260 256) (List.range' 260 256) (List.range' 4 256)
    secp256k1ReductionConstantBits (2 ^ 256 - (2 ^ 32 + 977)) 516 1 2 3 0
/-- One literal production circuit and its exact worst-case selected-correction events. -/
theorem secp256k1SquareSource_certificate :
    secp256k1SquareSource.erase=secp256k1Square ∧ secp256k1SquareSource.events=522242 := by
  constructor
  · exact squareLoopSource_erase _ _ _ _ _ _ _ _ _ _
  · have h := squareLoopSource_events (List.range' 260 256) (List.range' 260 256) 4 (List.range' 5 255)
      secp256k1ReductionConstantBits (2^256-(2^32+977)) 516 1 2 3 0 (by simp) (by decide +kernel)
    change secp256k1SquareSource.events=_ at h
    simpa only [List.length_range',List.length_cons,sourceProduction_threshold,if_false,sourceReduction_nonzero,Bool.false_eq_true] using h
def secp256k1SquareInverseSource : CorrectionProgram :=
  squareLoopInverseSource (List.range' 260 256) (List.range' 260 256) (List.range' 4 256)
    secp256k1ModulusBits (2^256-(2^32+977)) 516 1 2 3 0
/-- One literal production circuit and its exact worst-case selected-correction events. -/
theorem secp256k1SquareInverseSource_certificate :
    secp256k1SquareInverseSource.erase=secp256k1SquareInverse ∧ secp256k1SquareInverseSource.events=522242 := by
  constructor
  · exact squareLoopInverseSource_erase _ _ _ _ _ _ _ _ _ _
  · have h := squareLoopInverseSource_events (List.range' 260 256) (List.range' 260 256) 4 (List.range' 5 255)
      secp256k1ModulusBits (2^256-(2^32+977)) 516 1 2 3 0 (by simp) (by decide +kernel)
    change secp256k1SquareInverseSource.events=_ at h
    simpa only [List.length_range',List.length_cons,sourceProduction_threshold,if_false,sourceModulus_nonzero,Bool.false_eq_true] using h
end ShorECDLP.Paper2607_13816
