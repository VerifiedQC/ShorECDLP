import ShorECDLP.Framework.Quantum.Semantics
import Mathlib.Algebra.Group.Defs

namespace ShorECDLP

def ecdlpFunction
    {G : Type*} [AddCommGroup G]
    (P Q : G) (a b : ℕ) : G :=
  a • P + b • Q

--Assign every group element a w-bit classical code.
structure PointEncoding (G : Type*) (w : ℕ) where
  encode : G → Fin (2 ^ w)
  injective : Function.Injective encode

def ECDLPOracleSpec
    {G : Type*} [AddCommGroup G]
    {w : ℕ}
    (enc : PointEncoding G w)
    (oracle : Quantum.State →ₗ[ℂ] Quantum.State)
    (P Q : G)
    (aReg bReg pointReg : List Nat) : Prop :=
  ∀ s a b R,
    regValue aReg s = a →
    regValue bReg s = b →
    regValue pointReg s = (enc.encode R).val →
    oracle (Quantum.ket s) =
      Quantum.ket
        (writeReg pointReg
          (enc.encode (R + a • P + b • Q)).val s)

end ShorECDLP
