import ShorECDLP.Submission.«2607_13816».Window.TableLookup
import ShorECDLP.Submission.«2607_13816».Window.Recoding
namespace ShorECDLP.Paper2607_13816
/-- Magnitude-table address for centered odd digits. The high half is positive. -/
def signedTableAddress (half value : Nat) : Nat :=
  if value<half then half-1-value else value-half

def signedTableOdd (half value : Nat) : Int :=
  if value<half then -((2*signedTableAddress half value+1:Nat):Int)
  else ((2*signedTableAddress half value+1:Nat):Int)

theorem signedTableAddress_bound (half value : Nat) (hv : value<2*half) :
    signedTableAddress half value<half := by
  unfold signedTableAddress
  split <;> omega

theorem signedTableOdd_value (half value : Nat) :
    signedTableOdd half value=2*(value:Int)-2*(half:Int)+1 := by
  unfold signedTableOdd signedTableAddress
  split_ifs with h
  · have he : half-1-value+value+1=half := by omega
    have he' : ((half-1-value:Nat):Int)+(value:Int)+1=(half:Int) := by exact_mod_cast he
    push_cast
    omega
  · have he : value-half+half=value := by omega
    have he' : ((value-half:Nat):Int)+(half:Int)=(value:Int) := by exact_mod_cast he
    push_cast
    omega

/-- Odd multiples of a half-point use exactly half as many table entries.
The fixed extra half-point is independent of the digit. -/
theorem signedTable_point {G : Type} [AddCommGroup G] (Q : G)
    (half value : Nat) :
    signedTableOdd half value • Q - Q = ((value:Int)-(half:Int)) • (Q+Q) := by
  rw [signedTableOdd_value half value,smul_add]
  simp only [sub_zsmul,add_zsmul,one_zsmul]
  rw [show 2*(value:Int)=(value:Int)+(value:Int) by ring,
    show 2*(half:Int)=(half:Int)+(half:Int) by ring]
  simp only [add_zsmul]
  abel

/-- A concrete half-point in an odd-order cyclic subgroup. -/
def signedWindowHalfPoint {G : Type} [AddCommGroup G] (P : G) (r : Nat) : G :=
  ((r+1)/2) • P

theorem signedWindowHalfPoint_double {G : Type} [AddCommGroup G] (P : G) (r : Nat)
    (hr : Odd r) (hP : r • P=0) : signedWindowHalfPoint P r+signedWindowHalfPoint P r=P := by
  rcases hr with ⟨k,hk⟩
  have hn : (r+1)/2+(r+1)/2=r+1 := by omega
  rw [signedWindowHalfPoint,←add_nsmul,hn,add_nsmul,hP,one_nsmul,zero_add]

theorem signedTable16_address_bound (value : Nat) (hv : value<2^16) :
    signedTableAddress (2^15) value<2^15 :=
  signedTableAddress_bound _ _ hv

/-- Signed width-16 digits use 32,768 odd-multiple entries plus a fixed half-point offset. -/
theorem signedTable16_point {G : Type} [AddCommGroup G] (P : G) (r value : Nat)
    (hr : Odd r) (hP : r • P=0) :
    signedTableOdd (2^15) value • signedWindowHalfPoint P r - signedWindowHalfPoint P r =
      signedWindowDigit 16 value • P := by
  rw [signedTable_point,signedWindowHalfPoint_double P r hr hP]
  rfl

open Classical Quantum
noncomputable section
/-- Reflect the low address bits when the high sign bit is false and q is enabled. -/
def signedAddressCircuit (q sign : Wire) (bits : List Wire) : Circuit :=
  tableXorGates q bits ++ tableXorGates sign bits

def signedAddressState (q sign : Wire) (bits : List Wire) (s : BasisState) : BasisState :=
  tableXorState bits (s sign) (tableXorState bits (s q) s)

theorem signedAddressCircuit_run (q sign : Wire) (bits : List Wire) (hn : bits.Nodup)
    (hq : q∉bits) (hsign : sign∉bits) (s : BasisState) :
    Classical.run (signedAddressCircuit q sign bits) s=signedAddressState q sign bits s := by
  rw [signedAddressCircuit,Classical.run_append,run_tableXorGates q bits s hn hq,
    run_tableXorGates sign bits _ hn hsign]
  simp [signedAddressState,tableXorState,hsign]

theorem signedAddressState_frame (q sign : Wire) (bits : List Wire) (s : BasisState)
    (w : Wire) (hw : w∉bits) : signedAddressState q sign bits s w=s w := by
  simp [signedAddressState,tableXorState,hw]

theorem signedAddressState_involution (q sign : Wire) (bits : List Wire)
    (hq : q∉bits) (hsign : sign∉bits) (s : BasisState) :
    signedAddressState q sign bits (signedAddressState q sign bits s)=s := by
  have hq' := signedAddressState_frame q sign bits s q hq
  have hs' := signedAddressState_frame q sign bits s sign hsign
  funext w
  simp only [signedAddressState,tableXorState] at hq' hs' ⊢
  rw [hq',hs']
  cases s w <;> cases s q <;> cases s sign <;> cases decide (w∈bits) <;> rfl

theorem signedAddressState_word (q sign : Wire) (bits : List Wire) (s : BasisState) (hq : s q=true) :
    wireValues bits (signedAddressState q sign bits s)=
      if s sign then wireValues bits s else (wireValues bits s).map Bool.not := by
  cases hs : s sign
  · simp only [Bool.false_eq_true,if_false,wireValues,List.map_map]
    apply List.map_congr_left
    intro w hw
    simp [signedAddressState,tableXorState,hs,hq,hw]
  · simp only [if_true,wireValues]
    apply List.map_congr_left
    intro w hw
    simp [signedAddressState,tableXorState,hs,hq,hw]

theorem signedAddressCircuit_HPFree (q sign : Wire) (bits : List Wire) :
    HPFree (signedAddressCircuit q sign bits) := by
  simp [signedAddressCircuit,tableXorGates_HPFree]

theorem signedAddressCircuit_ket (q sign : Wire) (bits : List Wire) (hn : bits.Nodup)
    (hq : q∉bits) (hsign : sign∉bits) (s : BasisState) :
    Quantum.run (signedAddressCircuit q sign bits) (ket s)=ket (signedAddressState q sign bits s) := by
  rw [Quantum.run_ket_agrees_classical _ _ (signedAddressCircuit_HPFree q sign bits),
    signedAddressCircuit_run q sign bits hn hq hsign s]

theorem signedAddressCircuit_tCount (q sign : Wire) (bits : List Wire) :
    ShorECDLP.tCount (signedAddressCircuit q sign bits)=0 := by
  simp [signedAddressCircuit,tCount_append]
/-- The decoded reflected low word addresses the odd-multiple table. -/
theorem signedAddressState_value (q sign : Wire) (bits : List Wire) (s : BasisState) (hq : s q=true) :
    boolWordToNat (wireValues bits (signedAddressState q sign bits s))=
      signedTableAddress (2^bits.length)
        (boolWordToNat (wireValues bits s)+2^bits.length*(s sign).toNat) := by
  have hb := boolWordToNat_lt_pow_two (wireValues bits s)
  have hc := boolWordToNat_map_not_add (wireValues bits s)
  have hl : (wireValues bits s).length=bits.length := by simp [wireValues]
  rw [hl] at hb hc
  rw [signedAddressState_word q sign bits s hq]
  cases hs : s sign
  · simp only [Bool.false_eq_true,if_false,Bool.toNat_false,Nat.mul_zero,Nat.add_zero]
    rw [signedTableAddress,if_pos hb]
    omega
  · simp only [if_true,Bool.toNat_true,Nat.mul_one]
    rw [signedTableAddress,if_neg (by omega)]
    omega

theorem signedAddressCircuit_wellFormed (q sign : Wire) (bits : List Wire)
    (hq : q∉bits) (hsign : sign∉bits) : CircuitWellFormed (signedAddressCircuit q sign bits) := by
  exact List.forall_mem_append.mpr ⟨tableXorGates_wellFormed q bits hq,tableXorGates_wellFormed sign bits hsign⟩

theorem signedAddressCircuit_length (q sign : Wire) (bits : List Wire) :
    (signedAddressCircuit q sign bits).length=2*bits.length := by
  simp [signedAddressCircuit,tableXorGates]
  omega

end
end ShorECDLP.Paper2607_13816
