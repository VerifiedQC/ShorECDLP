import ShorECDLP.Submission.«2607_13816».Arithmetic.ConstantResourceCounts

namespace ShorECDLP.Paper2607_13816
open Classical Quantum

private theorem bits_value (k : Nat) (hk : k<ShorECDLP.p) : boolWordToNat (constantBits 256 k)=k := by
  rw [boolWordToNat_constantBits,Nat.mod_eq_of_lt]
  exact hk.trans (by decide +kernel)

def pointConstantT (k : Nat) : Nat := if k=0 then 10717 else 26803
def pointConstantMeasurements (k : Nat) : Nat := if k=0 then 511 else 1278

theorem fig14ConstantX_counts (k : Nat) (hk : k<ShorECDLP.p) :
    (fig14ConstantX k).tCount=pointConstantT k ∧
    (fig14ConstantX k).measurementCount=pointConstantMeasurements k := by
  have hh := uncontrolledConstantModularAdd256_counts (List.range' 263 256) (List.range' 7 256)
    (constantBits 256 k) 559 560 561 558 (by simp) (by simp) (by simp) (by rw [bits_value k hk]; exact hk)
  simpa only [fig14ConstantX,bits_value k hk,pointConstantT,pointConstantMeasurements] using hh

theorem fig14ControlledConstantX_counts (k : Nat) (hk : k<ShorECDLP.p) :
    (fig14ControlledConstantX k).tCount=pointConstantT k ∧
    (fig14ControlledConstantX k).measurementCount=pointConstantMeasurements k := by
  have hh := controlledConstantModularAdd256_counts (List.range' 263 256) (List.range' 7 256)
    (constantBits 256 k) 836 559 560 561 558 (by simp) (by simp) (by simp) (by rw [bits_value k hk]; exact hk)
  simpa only [fig14ControlledConstantX,bits_value k hk,pointConstantT,pointConstantMeasurements] using hh

theorem fig14ControlledConstantY_counts (k : Nat) (hk : k<ShorECDLP.p) :
    (fig14ControlledConstantY k).tCount=pointConstantT k ∧
    (fig14ControlledConstantY k).measurementCount=pointConstantMeasurements k := by
  have hh := controlledConstantModularAdd256_counts (List.range' 580 256) (List.range' 7 256)
    (constantBits 256 k) 836 559 560 561 558 (by simp) (by simp) (by simp) (by rw [bits_value k hk]; exact hk)
  simpa only [fig14ControlledConstantY,bits_value k hk,pointConstantT,pointConstantMeasurements] using hh

theorem fig14Negate_counts : fig14Negate.tCount=21434 ∧ fig14Negate.measurementCount=1022 := by
  have hbits : constantBits 256 ShorECDLP.p=secp256k1ModulusBits := by decide +kernel
  simpa only [fig14Negate,hbits] using controlledModularNegate256_counts
    (List.range' 263 256) (List.range' 7 256) 836 559 560 561 558 (by simp) (by simp)
end ShorECDLP.Paper2607_13816
