import ShorECDLP.Framework.Contract
import ShorECDLP.Submission.Correctness.Trial
import ShorECDLP.Submission.OrderFinding.Main
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Conditional secp256k1 order-finding theorem

This module applies the already-proved two-register order-finding theorem to
the concrete two-ScalarMul ECDLP oracle.  The result keeps the two remaining
secp256k1 group facts visible: primality of `order` and the statement that the
standard generator has that additive order.

The exact single-trial circuit is named explicitly so its correctness and
resource theorems refer to the same term.  The final theorem proves the closed
Framework `BitcoinECDLPSubmission` claim: 26 independent measured trials reach
99% success and charge 26 copies of that identical trial circuit.
-/

namespace ShorECDLP
namespace Secp256k1

variable [Fact (Nat.Prime p)] [Fact (Nat.Prime order)]

open Quantum.PhaseEstimation

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

omit [Fact (Nat.Prime p)] [Fact (Nat.Prime order)] in
private theorem hadamards_wellFormed (reg : List Wire) :
    CircuitWellFormed (hadamards reg) := by
  simp [hadamards, CircuitWellFormed, Gate.WellFormed]

omit [Fact (Nat.Prime order)] in
/-- The exact trial is a well-formed unitary circuit on a valid layout. -/
theorem ecdlpTrial_wellFormed
    (Q : Point)
    (aReg bReg pointReg : List Wire)
    (workStart qftAncilla : Wire)
    (s : BasisState)
    (hpointLength : pointReg.length = pointWidth)
    (hnodup :
      (aReg ++ bReg ++ pointReg ++ scalarMulWork workStart).Nodup)
    (hsetup :
      Quantum.OrderFinding.OrderFindingSetup pointEncoding
        aReg bReg pointReg (scalarMulWork workStart)
        qftAncilla 256 s) :
    CircuitWellFormed
      (ecdlpTrial aReg bReg pointReg workStart qftAncilla Q) := by
  have habc := hnodup.of_append_left
  have hab := habc.of_append_left
  have haNodup : aReg.Nodup := hab.of_append_left
  have hbNodup : bReg.Nodup := hab.of_append_right
  have hfresh := hsetup.ancilla_fresh
  simp only [List.mem_append, not_or] at hfresh
  simp only [ecdlpTrial, circuitWellFormed_append]
  exact ⟨⟨⟨hadamards_wellFormed (aReg ++ bReg),
      ecdlpOracle_wellFormed aReg bReg pointReg workStart G Q
        hpointLength hnodup⟩,
      Quantum.iqft_wellFormed aReg qftAncilla hfresh.1.1.1 haNodup⟩,
    Quantum.iqft_wellFormed bReg qftAncilla hfresh.1.1.2 hbNodup⟩

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

omit [Fact (Nat.Prime p)] [Fact (Nat.Prime order)] in
private theorem bitcoin_singleRun_lower :
    (41 / 250 : Real) ≤
      ((order - 1 : Real) / order) *
        ((4 : Real) / Real.pi ^ 2) ^ 2 := by
  have hpi : Real.pi < (3.1416 : Real) := Real.pi_lt_d4
  have hpipos : 0 < Real.pi := Real.pi_pos
  have hpi2 : Real.pi ^ 2 < (3.1416 : Real) ^ 2 := by
    nlinarith
  have hpi4 : Real.pi ^ 4 < (3.1416 : Real) ^ 4 := by
    nlinarith [sq_nonneg (Real.pi ^ 2),
      sq_nonneg ((3.1416 : Real) ^ 2)]
  have horderpos : (0 : Real) < order := by
    norm_num [order]
  have hpine : Real.pi ≠ 0 := ne_of_gt hpipos
  have hordne : (order : Real) ≠ 0 := ne_of_gt horderpos
  field_simp [hpine, hordne]
  norm_num [order] at hpi4 ⊢
  nlinarith

omit [Fact (Nat.Prime p)] [Fact (Nat.Prime order)] in
/--
The public Bitcoin ECDLP submission theorem.

The exact 256-bit `ecdlpTrial` is run and measured independently 26 times.
Canonical postprocessing recovers `d` with probability at least 99%, and the
same 26 trial circuits have exact aggregate T-count 21,888,426,033,809,920.
-/
theorem bitcoinECDLP_correct
    : BitcoinECDLPSubmission := by
  unfold BitcoinECDLPSubmission
  intro _ _ d Q aReg bReg pointReg workStart qftAncilla s
    hpointLength hnodup horderG hQ hQnonzero hsetup
  have hwf := ecdlpTrial_wellFormed
    Q aReg bReg pointReg workStart qftAncilla s
    hpointLength hnodup hsetup
  have hnorm :
      Quantum.normSq
        (Quantum.run
          (ecdlpTrial aReg bReg pointReg workStart qftAncilla Q)
          (Quantum.ket s)) = 1 :=
    Quantum.normSq_run_ket _ hwf s
  refine ⟨hnorm, ?_, ?_⟩
  · have hsingleExact := orderFinding_correct
      Q aReg bReg pointReg workStart qftAncilla s
      hpointLength hnodup horderG hQ hsetup (by norm_num [order])
    have hsingle :
        (41 / 250 : Real) ≤
          Quantum.OrderFinding.orderFindingSuccessProbability
            order 256 d (Fact.out : Nat.Prime order) aReg bReg
            (Quantum.run
              (ecdlpTrial aReg bReg pointReg workStart qftAncilla Q)
              (Quantum.ket s)) :=
      bitcoin_singleRun_lower.trans hsingleExact
    have hleNorm :=
      Quantum.OrderFinding.orderFindingSuccessProbability_le_normSq
        order 256 d (Fact.out : Nat.Prime order)
        aReg bReg hsetup.a_width hsetup.b_width
        (Quantum.run
          (ecdlpTrial aReg bReg pointReg workStart qftAncilla Q)
          (Quantum.ket s))
    have hsingleLeOne :
        Quantum.OrderFinding.orderFindingSuccessProbability
            order 256 d (Fact.out : Nat.Prime order) aReg bReg
            (Quantum.run
              (ecdlpTrial aReg bReg pointReg workStart qftAncilla Q)
              (Quantum.ket s)) ≤ 1 :=
      hleNorm.trans_eq hnorm
    have hamp := independentRetrySuccessProbability_mono
      26 hsingleLeOne hsingle
    have hnumeric :
        (99 / 100 : Real) ≤
          independentRetrySuccessProbability (41 / 250 : Real) 26 := by
      norm_num [independentRetrySuccessProbability]
    exact hnumeric.trans hamp
  · unfold repeatedTCount
    rw [ecdlpTrial_tCount Q aReg bReg pointReg workStart qftAncilla
      hsetup.a_width hsetup.b_width hpointLength horderG hQ hQnonzero]

end Secp256k1
end ShorECDLP
