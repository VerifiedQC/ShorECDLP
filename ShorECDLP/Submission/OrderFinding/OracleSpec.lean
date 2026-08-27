import ShorECDLP.Framework.Contract

namespace ShorECDLP

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
