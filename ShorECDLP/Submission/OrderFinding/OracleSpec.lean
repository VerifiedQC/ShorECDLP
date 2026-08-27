import ShorECDLP.Framework.Quantum.InnerProduct
import ShorECDLP.Framework.BasisState

namespace ShorECDLP

/-- An injective fixed-width representation of mathematical group elements. -/
structure PointEncoding (G : Type*) (w : Nat) where
  encode : G → Fin (2 ^ w)
  injective : Function.Injective encode

/-- The classical ECDLP oracle function `(a,b,R) ↦ R + aP + bQ`. -/
def ecdlpFunction {G : Type*} [AddCommGroup G]
    (P Q : G) (a b : Nat) : G :=
  a • P + b • Q

structure ECDLPOracleSpec
    {G : Type*} [AddCommGroup G]
    {w : ℕ}
    (enc : PointEncoding G w)
    (oracle : Quantum.State →ₗ[ℂ] Quantum.State)
    (P Q : G)
    (aReg bReg pointReg oracleWork : List Nat) : Prop where

  point_width : pointReg.length = w

  registers_nodup :
    (aReg ++ bReg ++ pointReg ++ oracleWork).Nodup

  preservesInner :
    Quantum.PreservesInner oracle

  onKet :
    ∀ (s : BasisState) (a b : ℕ) (R : G),
      regValue aReg s = a →
      regValue bReg s = b →
      regValue pointReg s = (enc.encode R).val →
      Clean oracleWork s →
      oracle (Quantum.ket s) =
        Quantum.ket
          (writeReg pointReg
            (enc.encode (R + ecdlpFunction P Q a b)).val s)

end ShorECDLP
