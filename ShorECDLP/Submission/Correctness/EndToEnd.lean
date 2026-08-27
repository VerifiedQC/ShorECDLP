import ShorECDLP.Submission.EllipticCurve.ECDLPOracle
import ShorECDLP.Submission.OrderFinding.Main

/-!
# Conditional secp256k1 order-finding theorem

This module applies the already-proved two-register order-finding theorem to
the concrete two-ScalarMul ECDLP oracle.  The result keeps the two remaining
secp256k1 group facts visible: primality of `order` and the statement that the
standard generator has that additive order.

The exact single-trial circuit is named explicitly so its correctness and
resource theorems refer to the same term.  Classical repetition to the final
99% success target is packaged separately at the framework boundary.
-/

namespace ShorECDLP
namespace Secp256k1

variable [Fact (Nat.Prime p)] [Fact (Nat.Prime order)]

open Quantum.PhaseEstimation

/-- One exact secp256k1 ECDLP order-finding trial. -/
def ecdlpTrial
    (aReg bReg pointReg : List Wire)
    (workStart qftAncilla : Wire)
    (Q : Point) : Circuit :=
  hadamards (aReg ++ bReg) ++
    ecdlpOracle aReg bReg pointReg workStart G Q ++
    Quantum.iqft aReg qftAncilla ++
    Quantum.iqft bReg qftAncilla

omit [Fact (Nat.Prime order)] in
/-- The named trial is definitionally the circuit form of `orderFinding`. -/
theorem ecdlpTrial_run
    (aReg bReg pointReg : List Wire)
    (workStart qftAncilla : Wire)
    (Q : Point) (s : BasisState) :
    Quantum.run (ecdlpTrial
        aReg bReg pointReg workStart qftAncilla Q) (Quantum.ket s) =
      Quantum.OrderFinding.orderFinding
        aReg bReg qftAncilla
        (Quantum.run
          (ecdlpOracle aReg bReg pointReg workStart G Q))
        (Quantum.ket s) := by
  simp [ecdlpTrial, Quantum.OrderFinding.orderFinding,
    Quantum.run_append, LinearMap.comp_apply]

omit [Fact (Nat.Prime order)] in
private theorem scalarMulTable_ne_zero_of_order
    (scalarReg : List Wire) (P : Point)
    (hlength : scalarReg.length = 256)
    (horder : addOrderOf P = order) :
    ∀ C ∈ scalarMulTable scalarReg P, C ≠ 0 := by
  rw [List.forall_mem_iff_get]
  intro i
  simp only [scalarMulTable, Precompute.doublingTable_get]
  intro hzero
  have hdvd : order ∣ 2 ^ (i : Nat) := by
    rw [← horder]
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr hzero
  have hi : (i : Nat) < 256 := by
    have hi' := i.isLt
    simpa [scalarMulTable, hlength] using hi'
  have hpow : 2 ^ (i : Nat) < order := by
    calc
      2 ^ (i : Nat) ≤ 2 ^ 255 :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      _ < order := by norm_num [order]
  exact (Nat.not_le_of_gt hpow)
    (Nat.le_of_dvd (by positivity) hdvd)

private theorem publicKey_order
    {d : Nat} (Q : Point)
    (horderG : addOrderOf G = order)
    (hQ : Q = d • G)
    (hQnonzero : Q ≠ 0) :
    addOrderOf Q = order := by
  have hdnot : ¬ order ∣ d := by
    intro hd
    have hdsmul : d • G = 0 := by
      rw [← addOrderOf_dvd_iff_nsmul_eq_zero, horderG]
      exact hd
    exact hQnonzero (hQ.trans hdsmul)
  have hcoprime : order.Coprime d :=
    ((Fact.out : Nat.Prime order).coprime_iff_not_dvd).2 hdnot
  have hcoprimeG : (addOrderOf G).Coprime d := by
    simpa [horderG] using hcoprime
  calc
    addOrderOf Q = addOrderOf (d • G) := congrArg addOrderOf hQ
    _ = addOrderOf G := hcoprimeG.addOrderOf_nsmul
    _ = order := horderG

omit [Fact (Nat.Prime p)] [Fact (Nat.Prime order)] in
private theorem hadamards_tCount (reg : List Wire) :
    tCount (hadamards reg) = 0 := by
  induction reg with
  | nil => rfl
  | cons w ws ih =>
      rw [hadamards, List.map_cons, tCount_cons]
      have ih' : tCount (List.map Gate.H ws) = 0 := by
        simpa only [hadamards] using ih
      simpa only [tCost, zero_add] using ih'

/--
The concrete secp256k1 oracle satisfies the conditional ECDLP order-finding
success bound.  The generator-order equality and the relation `Q = d • G`
remain explicit hypotheses.
-/
theorem orderFinding_correct
    {d precision : Nat}
    (Q : Point)
    (aReg bReg pointReg : List Wire)
    (workStart qftAncilla : Wire)
    (s : BasisState)
    (hpointLength : pointReg.length = pointWidth)
    (hnodup :
      (aReg ++ bReg ++ pointReg ++ scalarMulWork workStart).Nodup)
    (horderG : addOrderOf G = order)
    (hQ : Q = d • G)
    (hsetup :
      Quantum.OrderFinding.OrderFindingSetup pointEncoding
        aReg bReg pointReg (scalarMulWork workStart)
        qftAncilla precision s)
    (hprecision : order ≤ 2 ^ precision) :
    ((order - 1 : ℝ) / order) *
        ((4 : ℝ) / Real.pi ^ 2) ^ 2 ≤
      Quantum.OrderFinding.orderFindingSuccessProbability
        order precision d (Fact.out : Nat.Prime order)
        aReg bReg
        (Quantum.run
          (ecdlpTrial
            aReg bReg pointReg workStart qftAncilla Q)
          (Quantum.ket s)) := by
  let hsetting :
      Quantum.OrderFinding.ECDLPSetting G Q order d :=
    { prime_order := (Fact.out : Nat.Prime order)
      order_P := horderG
      Q_eq := hQ }

  have hspec := ecdlpOracle_spec
    aReg bReg pointReg workStart G Q hpointLength hnodup

  have hresult := Quantum.OrderFinding.orderFinding_correct
    pointEncoding
    (Quantum.run (ecdlpOracle aReg bReg pointReg workStart G Q))
    G Q aReg bReg pointReg (scalarMulWork workStart)
    qftAncilla s hsetting hspec hsetup hprecision

  simpa [hsetting, ecdlpTrial_run] using hresult

/--
Exact single-trial T-count at the 256-bit Bitcoin precision.  Nonzeroness of
the public key rules out the point-at-infinity shortcut in its doubling table.
-/
theorem ecdlpTrial_tCount
    {d : Nat} (Q : Point)
    (aReg bReg pointReg : List Wire)
    (workStart qftAncilla : Wire)
    (haLength : aReg.length = 256)
    (hbLength : bReg.length = 256)
    (hpointLength : pointReg.length = pointWidth)
    (horderG : addOrderOf G = order)
    (hQ : Q = d • G)
    (hQnonzero : Q ≠ 0) :
    tCount (ecdlpTrial
      aReg bReg pointReg workStart qftAncilla Q) =
      841862539761920 := by
  have hGTable := scalarMulTable_ne_zero_of_order
    aReg G haLength horderG
  have horderQ := publicKey_order Q horderG hQ hQnonzero
  have hQTable := scalarMulTable_ne_zero_of_order
    bReg Q hbLength horderQ
  rw [ecdlpTrial, tCount_append, tCount_append, tCount_append,
    hadamards_tCount,
    ecdlpOracle_tCount_of_tables_ne_zero
      aReg bReg pointReg workStart G Q hpointLength hGTable hQTable,
    Quantum.tCount_iqft, Quantum.tCount_iqft,
    haLength, hbLength]

end Secp256k1
end ShorECDLP
