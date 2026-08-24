import ShorECDLP.Framework.Quantum.InnerProduct
import ShorECDLP.Framework.BasisState

namespace ShorECDLP

structure PointEncoding (G : Type*) (w : ℕ) where
  encode : G → Fin (2 ^ w)
  injective : Function.Injective encode

def ecdlpFunction {G : Type*} [AddCommGroup G]
    (P Q : G) (a b : ℕ) : G :=
  a • P + b • Q

structure ECDLPOracleSpec
    {G : Type*} [AddCommGroup G]
    {w : ℕ}
    (enc : PointEncoding G w)
    (oracle : Quantum.State →ₗ[ℂ] Quantum.State)
    (P Q : G)
    (aReg bReg pointReg : List Nat) : Prop where

  point_width : pointReg.length = w

  registers_nodup : (aReg ++ bReg ++ pointReg).Nodup

  preservesInner : Quantum.PreservesInner oracle

  onKet :
    ∀ (s : BasisState) (a b : ℕ) (R : G),
      regValue aReg s = a → regValue bReg s = b →
      regValue pointReg s = (enc.encode R).val →
      oracle (Quantum.ket s)
        =
      Quantum.ket (writeReg pointReg
        (enc.encode (R + ecdlpFunction P Q a b)).val s)

end ShorECDLP
