import ShorECDLP.Framework.Contract
import ShorECDLP.Framework.Repetition
import ShorECDLP.Submission.EllipticCurve.GeneratorOrder
import ShorECDLP.Submission.Correctness.Trial
import ShorECDLP.Submission.OrderFinding.Main
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Conditional secp256k1 order-finding theorem

This module applies the already-proved two-register order-finding theorem to
the concrete two-ScalarMul ECDLP oracle.  Primality of `p` and `order`, and the
statement that the standard generator has additive order `order`, are
discharged by the certificate module.

The exact single-trial circuit is named explicitly so its correctness and
resource theorems refer to the same term.  This module supplies the proofs used
by the concrete record in `Submission/Submission.lean` and derives the exact
aggregate count for 26 measured trials.
-/

namespace ShorECDLP
namespace Secp256k1

/- The concrete base-field certificate is available only while elaborating this
module; importing `EndToEnd` does not install a global primality instance. -/
local instance : Fact (Nat.Prime p) := ⟨p_prime⟩

open Quantum.PhaseEstimation

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
    (hQ : Q = d • G)
    (hQnonzero : Q ≠ 0) :
    addOrderOf Q = order := by
  have hdnot : ¬ order ∣ d := by
    intro hd
    have hdsmul : d • G = 0 := by
      rw [← addOrderOf_dvd_iff_nsmul_eq_zero, generator_order]
      exact hd
    exact hQnonzero (hQ.trans hdsmul)
  have hcoprime : order.Coprime d :=
    order_prime.coprime_iff_not_dvd.2 hdnot
  have hcoprimeG : (addOrderOf G).Coprime d := by
    simpa [generator_order] using hcoprime
  calc
    addOrderOf Q = addOrderOf (d • G) := congrArg addOrderOf hQ
    _ = addOrderOf G := hcoprimeG.addOrderOf_nsmul
    _ = order := generator_order

private theorem hadamards_tCount (reg : List Wire) :
    tCount (hadamards reg) = 0 := by
  induction reg with
  | nil => rfl
  | cons w ws ih =>
      rw [hadamards, List.map_cons, tCount_cons]
      have ih' : tCount (List.map Gate.H ws) = 0 := by
        simpa only [hadamards] using ih
      simpa only [tCost, zero_add] using ih'

private theorem hadamards_usesOnly (reg : List Wire) :
    CircuitUsesOnly reg (hadamards reg) := by
  intro g hg
  simp only [hadamards, List.mem_map] at hg
  obtain ⟨w, hw, rfl⟩ := hg
  simpa [Gate.UsesOnly] using hw

private theorem gateAdjoint_usesOnly
    {support : List Wire} {g : Gate}
    (h : g.UsesOnly support) :
    g.adjoint.UsesOnly support := by
  cases g <;> simpa [Gate.UsesOnly] using h

private theorem circuitAdjoint_usesOnly
    {support : List Wire} {c : Circuit}
    (h : CircuitUsesOnly support c) :
    CircuitUsesOnly support (Circuit.adjoint c) := by
  induction c with
  | nil => simp [Circuit.adjoint, CircuitUsesOnly]
  | cons g c ih =>
      rw [circuit_adjoint_cons]
      apply Arithmetic.usesOnly_append
      · exact ih (fun gate hgate =>
          h gate (List.mem_cons_of_mem g hgate))
      · intro gate hgate
        simp only [List.mem_singleton] at hgate
        subst gate
        exact gateAdjoint_usesOnly
          (h g (List.mem_cons_self ..))

private theorem cPhase_usesOnly
    (k : Nat) (control target ancilla : Wire) :
    CircuitUsesOnly [control, target, ancilla]
      (Quantum.cPhase k control target ancilla) := by
  simp [Quantum.cPhase, CircuitUsesOnly, Gate.UsesOnly]

private theorem qftPhaseLayer_usesOnly
    (target ancilla : Wire) :
    ∀ (controls : List Wire) (k : Nat),
      CircuitUsesOnly (controls ++ [target, ancilla])
        (Quantum.qftPhaseLayer target ancilla controls k) := by
  intro controls
  induction controls with
  | nil =>
      intro k
      simp [Quantum.qftPhaseLayer, CircuitUsesOnly]
  | cons control controls ih =>
      intro k
      rw [Quantum.qftPhaseLayer]
      apply Arithmetic.usesOnly_append
      · apply Arithmetic.usesOnly_mono
          (cPhase_usesOnly k control target ancilla)
        intro w hw
        simp only [List.mem_cons, List.mem_append,
          List.not_mem_nil, or_false] at hw ⊢
        tauto
      · apply Arithmetic.usesOnly_mono (ih (k + 1))
        intro w hw
        simp only [List.mem_append, List.mem_cons] at hw ⊢
        tauto

private theorem qftCoreMSB_usesOnly
    (ancilla : Wire) :
    ∀ (reg : List Wire),
      CircuitUsesOnly (reg ++ [ancilla])
        (Quantum.qftCoreMSB ancilla reg) := by
  intro reg
  induction reg with
  | nil => simp [Quantum.qftCoreMSB, CircuitUsesOnly]
  | cons target rest ih =>
      rw [Quantum.qftCoreMSB]
      apply Arithmetic.usesOnly_append
      · apply Arithmetic.usesOnly_append
        · intro g hg
          simp only [List.mem_singleton] at hg
          subst g
          simp [Gate.UsesOnly]
        · apply Arithmetic.usesOnly_mono
            (qftPhaseLayer_usesOnly target ancilla rest 2)
          intro w hw
          simp only [List.mem_append, List.mem_cons,
            List.not_mem_nil, or_false] at hw ⊢
          tauto
      · apply Arithmetic.usesOnly_mono ih
        intro w hw
        simp only [List.mem_append, List.mem_cons] at hw ⊢
        tauto

private theorem qftCore_usesOnly
    (reg : List Wire) (ancilla : Wire) :
    CircuitUsesOnly (reg ++ [ancilla])
      (Quantum.qftCore reg ancilla) := by
  apply Arithmetic.usesOnly_mono
    (qftCoreMSB_usesOnly ancilla reg.reverse)
  intro w hw
  simp only [List.mem_append] at hw ⊢
  rcases hw with hreg | hancilla
  · exact Or.inl (by simpa using hreg)
  · exact Or.inr hancilla

private theorem bitReverse_usesOnly
    (reg : List Wire) :
    CircuitUsesOnly reg (Quantum.bitReverse reg) := by
  intro g hg
  simp only [Quantum.bitReverse, List.mem_flatMap] at hg
  obtain ⟨pair, hpairTake, hg⟩ := hg
  have hpair : pair ∈ reg.zip reg.reverse :=
    List.mem_of_mem_take hpairTake
  have hleft : pair.1 ∈ reg := (List.of_mem_zip hpair).1
  have hright : pair.2 ∈ reg := by
    simpa using (List.of_mem_zip hpair).2
  have hswap : CircuitUsesOnly reg
      (Quantum.swap pair.1 pair.2) := by
    simp [Quantum.swap, CircuitUsesOnly, Gate.UsesOnly,
      hleft, hright]
  exact hswap g hg

private theorem iqft_usesOnly
    (reg : List Wire) (ancilla : Wire) :
    CircuitUsesOnly (reg ++ [ancilla])
      (Quantum.iqft reg ancilla) := by
  apply circuitAdjoint_usesOnly
  rw [Quantum.qft]
  apply Arithmetic.usesOnly_append
  · exact qftCore_usesOnly reg ancilla
  · apply Arithmetic.usesOnly_mono
      (bitReverse_usesOnly reg)
    intro w hw
    exact List.mem_append_left [ancilla] hw

private theorem hadamards_wellFormed (reg : List Wire) :
    CircuitWellFormed (hadamards reg) := by
  simp [hadamards, CircuitWellFormed, Gate.WellFormed]

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
success bound.  The public-key relation `Q = d • G` remains an explicit
hypothesis.
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
    (hQ : Q = d • G)
    (hsetup :
      Quantum.OrderFinding.OrderFindingSetup pointEncoding
        aReg bReg pointReg (scalarMulWork workStart)
        qftAncilla precision s)
    (hprecision : order ≤ 2 ^ precision) :
    ((order - 1 : ℝ) / order) *
        ((4 : ℝ) / Real.pi ^ 2) ^ 2 ≤
      Quantum.OrderFinding.orderFindingSuccessProbability
        order precision d order_prime
        aReg bReg
        (Quantum.run
          (ecdlpTrial
            aReg bReg pointReg workStart qftAncilla Q)
          (Quantum.ket s)) := by
  let hsetting :
      Quantum.OrderFinding.ECDLPSetting G Q order d :=
    { prime_order := order_prime
      order_P := generator_order
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
    (hQ : Q = d • G)
    (hQnonzero : Q ≠ 0) :
    tCount (ecdlpTrial
      aReg bReg pointReg workStart qftAncilla Q) =
      841862539761920 := by
  have hGTable := scalarMulTable_ne_zero_of_order
    aReg G haLength generator_order
  have horderQ := publicKey_order Q hQ hQnonzero
  have hQTable := scalarMulTable_ne_zero_of_order
    bReg Q hbLength horderQ
  rw [ecdlpTrial, tCount_append, tCount_append, tCount_append,
    hadamards_tCount,
    ecdlpOracle_tCount_of_tables_ne_zero
      aReg bReg pointReg workStart G Q hpointLength hGTable hQTable,
    Quantum.tCount_iqft, Quantum.tCount_iqft,
    haLength, hbLength]

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

/--
The exact 256-bit `ecdlpTrial` meets the four single-trial proof fields used by
the Bitcoin submission record.
-/
theorem bitcoinECDLPTrial_correct
    {d : Nat} (Q : Point)
    (aReg bReg pointReg : List Wire)
    (workStart qftAncilla : Wire)
    (hpointLength : pointReg.length = pointWidth)
    (hnodup :
      (aReg ++ bReg ++ pointReg ++ scalarMulWork workStart).Nodup)
    (hQ : Q = d • G)
    (hsetup :
      Quantum.OrderFinding.OrderFindingSetup pointEncoding
        aReg bReg pointReg (scalarMulWork workStart)
        qftAncilla 256 zeroBasisState) :
    0 ≤ (41 / 250 : Real) ∧
    (41 / 250 : Real) ≤ 1 ∧
    Quantum.normSq
      (Quantum.run
        (ecdlpTrial aReg bReg pointReg workStart qftAncilla Q)
        (Quantum.ket zeroBasisState)) = 1 ∧
    (41 / 250 : Real) ≤
      ∑ a : Fin (2 ^ 256),
        ∑ b : Fin (2 ^ 256),
          if Quantum.OrderFinding.orderFindingPostprocess
              order 256 order_prime (a, b) =
              some (d : ZMod order)
          then
            Quantum.OrderFinding.jointRegisterProbability
              aReg bReg a.val b.val
              (Quantum.run
                (ecdlpTrial aReg bReg pointReg workStart qftAncilla Q)
                (Quantum.ket zeroBasisState))
          else 0 := by
  have hwf := ecdlpTrial_wellFormed
    Q aReg bReg pointReg workStart qftAncilla zeroBasisState
    hpointLength hnodup hsetup
  have hnorm :
      Quantum.normSq
        (Quantum.run
          (ecdlpTrial aReg bReg pointReg workStart qftAncilla Q)
          (Quantum.ket zeroBasisState)) = 1 :=
    Quantum.normSq_run_ket _ hwf zeroBasisState
  refine ⟨by norm_num, by norm_num, hnorm, ?_⟩
  exact bitcoin_singleRun_lower.trans <| orderFinding_correct
    Q aReg bReg pointReg workStart qftAncilla zeroBasisState
    hpointLength hnodup hQ hsetup (by norm_num [order])

/--
The proposed one-run lower bound `41/250` and trial count `26` give at least
99% success under independent measured repetition.
-/
theorem bitcoinECDLP_correct :
    (99 / 100 : Real) ≤ 1 - (1 - (41 / 250 : Real)) ^ (26 : Nat) := by
  norm_num

private theorem ecdlpTrial_usesOnly
    (Q : Point)
    (aReg bReg pointReg : List Wire)
    (workStart qftAncilla : Wire) :
    CircuitUsesOnly
      (aReg ++ bReg ++ pointReg ++ scalarMulWork workStart ++
        [qftAncilla])
      (ecdlpTrial aReg bReg pointReg workStart qftAncilla Q) := by
  let support :=
    aReg ++ bReg ++ pointReg ++ scalarMulWork workStart ++
      [qftAncilla]
  have hhadamards :
      CircuitUsesOnly support (hadamards (aReg ++ bReg)) := by
    apply Arithmetic.usesOnly_mono
      (hadamards_usesOnly (aReg ++ bReg))
    intro w hw
    simp only [support, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hw ⊢
    tauto
  have horacle : CircuitUsesOnly support
      (ecdlpOracle aReg bReg pointReg workStart G Q) := by
    apply Arithmetic.usesOnly_mono
      (ecdlpOracle_usesOnly
        aReg bReg pointReg workStart G Q)
    intro w hw
    simp only [support, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hw ⊢
    tauto
  have hiqftA : CircuitUsesOnly support
      (Quantum.iqft aReg qftAncilla) := by
    apply Arithmetic.usesOnly_mono
      (iqft_usesOnly aReg qftAncilla)
    intro w hw
    simp only [support, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hw ⊢
    tauto
  have hiqftB : CircuitUsesOnly support
      (Quantum.iqft bReg qftAncilla) := by
    apply Arithmetic.usesOnly_mono
      (iqft_usesOnly bReg qftAncilla)
    intro w hw
    simp only [support, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hw ⊢
    tauto
  have htotal := Arithmetic.usesOnly_append
    (Arithmetic.usesOnly_append
      (Arithmetic.usesOnly_append hhadamards horacle) hiqftA)
    hiqftB
  simpa [ecdlpTrial, support] using htotal

/-! ## Closed submission wire layout -/

/-- The first 256-bit phase register of the concrete submission. -/
def bitcoinAReg : List Wire :=
  List.range' 0 256

/-- The second 256-bit phase register of the concrete submission. -/
def bitcoinBReg : List Wire :=
  List.range' 256 256

/-- The 513-bit encoded-point register of the concrete submission. -/
def bitcoinPointReg : List Wire :=
  List.range' 512 pointWidth

/-- The QFT ancilla, placed between the public registers and the workspace. -/
def bitcoinQFTAncilla : Wire :=
  1025

/-- The first workspace wire, immediately after the QFT ancilla. -/
def bitcoinWorkStart : Wire :=
  1026

/-- Certified static qubit capacity of the current, non-reusing Bitcoin
allocation.  Every wire used by one trial has an index below this value. -/
def bitcoinQubitCount : Nat :=
  1394478

/-- Dense physical-wire envelope used to certify the current allocation. -/
private def bitcoinAllWires : List Wire :=
  List.range bitcoinQubitCount

private theorem bitcoinAllWires_length :
    bitcoinAllWires.length = bitcoinQubitCount := by
  simp [bitcoinAllWires]

private theorem blocksWires_upper
    (blocks : List Secp256k1Instance.Block)
    (limit : Nat)
    (hids : ∀ block ∈ blocks, block.id < limit) :
    ∀ w ∈ Secp256k1Instance.blocksWires blocks,
      w < Secp256k1Instance.fieldWidth * limit := by
  intro w hw
  simp only [Secp256k1Instance.blocksWires,
    List.mem_flatMap] at hw
  obtain ⟨block, hblock, hwire⟩ := hw
  have hbound := Secp256k1Instance.Block.mem_bounds hwire
  calc
    w < Secp256k1Instance.fieldWidth * (block.id + 1) :=
      hbound.2
    _ ≤ Secp256k1Instance.fieldWidth * limit :=
      Nat.mul_le_mul_left _ (Nat.succ_le_iff.mpr (hids block hblock))

private theorem secpAddLayout_upper :
    ∀ w ∈ Secp256k1Instance.secpAddLayout.allWires,
      w < Secp256k1Instance.fieldWidth * 5402 := by
  let blocks :=
    [Secp256k1Instance.regBlock Secp256k1Instance.baseId,
      Secp256k1Instance.regBlock Secp256k1Instance.exponentId,
      Secp256k1Instance.regBlock Secp256k1Instance.outId] ++
      Secp256k1Instance.addScratchBlocks
        Secp256k1Instance.initialAccId
  have hlayout :
      Secp256k1Instance.secpAddLayout.allWires =
        Secp256k1Instance.blocksWires blocks := by
    simp [blocks, Secp256k1Instance.secpAddLayout,
      RegisterLayout.allWires, Secp256k1Instance.addWork,
      Secp256k1Instance.reg, Secp256k1Instance.blocksWires,
      List.append_assoc]
  rw [hlayout]
  apply blocksWires_upper blocks 5402
  intro block hblock
  simp only [blocks, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hblock
  rcases hblock with (rfl | rfl | rfl) | hblock
  · norm_num [Secp256k1Instance.baseId]
  · norm_num [Secp256k1Instance.exponentId]
  · norm_num [Secp256k1Instance.outId]
  · simp [Secp256k1Instance.addScratchBlocks] at hblock
    rcases hblock with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num [Secp256k1Instance.initialAccId]

private theorem secpMulLayout_upper :
    ∀ w ∈ Secp256k1Instance.secpMulLayout.allWires,
      w < Secp256k1Instance.fieldWidth * 5402 := by
  let blocks :=
    [Secp256k1Instance.regBlock Secp256k1Instance.baseId,
      Secp256k1Instance.regBlock Secp256k1Instance.exponentId,
      Secp256k1Instance.regBlock Secp256k1Instance.outId,
      Secp256k1Instance.regBlock Secp256k1Instance.initialAccId] ++
      Secp256k1Instance.mulPrivateBlocks
        Secp256k1Instance.historyStartId
        Secp256k1Instance.fieldWidth
  have hlayout :
      Secp256k1Instance.secpMulLayout.allWires =
        Secp256k1Instance.blocksWires blocks := by
    simp [blocks, Secp256k1Instance.secpMulLayout,
      RegisterLayout.allWires, Secp256k1Instance.mulWork,
      Secp256k1Instance.reg, Secp256k1Instance.blocksWires,
      List.append_assoc]
  rw [hlayout]
  apply blocksWires_upper blocks 5402
  intro block hblock
  simp only [blocks, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hblock
  rcases hblock with (rfl | rfl | rfl | rfl) | hprivate
  · norm_num [Secp256k1Instance.baseId]
  · norm_num [Secp256k1Instance.exponentId]
  · norm_num [Secp256k1Instance.outId]
  · norm_num [Secp256k1Instance.initialAccId]
  · have hid : block.id ∈
        (Secp256k1Instance.mulPrivateBlocks
          Secp256k1Instance.historyStartId
          Secp256k1Instance.fieldWidth).map
            Secp256k1Instance.Block.id :=
        List.mem_map_of_mem hprivate
    rw [Secp256k1Instance.mulPrivateBlocks_ids] at hid
    have hbound := List.mem_range'_1.mp hid
    norm_num [Secp256k1Instance.historyStartId,
      Secp256k1Instance.fieldWidth] at hbound ⊢
    omega

private theorem secpLayout_upper :
    ∀ w ∈ Secp256k1Instance.secpLayout.allWires,
      w < Secp256k1Instance.fieldWidth * 5402 := by
  rw [Secp256k1Instance.secpLayout,
    Secp256k1Instance.secpPlan_allWires]
  apply blocksWires_upper Secp256k1Instance.secpLayoutBlocks 5402
  intro block hblock
  have hid : block.id ∈
      Secp256k1Instance.secpLayoutBlocks.map
        Secp256k1Instance.Block.id :=
    List.mem_map_of_mem hblock
  rw [Secp256k1Instance.secpLayoutBlocks_ids] at hid
  have hbound := List.mem_range'_1.mp hid
  have hlimit :
      Secp256k1Instance.mulStartId +
          18 * Secp256k1Instance.fieldWidth = 5402 := by
    unfold Secp256k1Instance.mulStartId
      Secp256k1Instance.mulAccId
      Secp256k1Instance.duplicateId
      Secp256k1Instance.historyStartId
    rw [Secp256k1Instance.historyCount_eq]
    norm_num [Secp256k1Instance.fieldWidth]
  rw [hlimit] at hbound
  exact hbound.2

private theorem pointAddArithmeticWork_upper :
    ∀ w ∈ pointAddArithmeticWork 2052,
      w < bitcoinQubitCount := by
  intro w hw
  simp only [pointAddArithmeticWork, List.mem_dedup,
    List.mem_append] at hw
  rcases hw with (hadd | hmul) | hexp
  · simp only [shiftWires, List.mem_map] at hadd
    obtain ⟨source, hsource, rfl⟩ := hadd
    have hsourceUpper := secpAddLayout_upper source hsource
    have hoffset : pointAddArithmeticOffset 2052 = 6164 := rfl
    calc
      pointAddArithmeticOffset 2052 + source <
          6164 + Secp256k1Instance.fieldWidth * 5402 := by
        rw [hoffset]
        exact Nat.add_lt_add_left hsourceUpper 6164
      _ = bitcoinQubitCount := by
        norm_num [bitcoinQubitCount,
          Secp256k1Instance.fieldWidth]
  · simp only [shiftWires, List.mem_map] at hmul
    obtain ⟨source, hsource, rfl⟩ := hmul
    have hsourceUpper := secpMulLayout_upper source hsource
    have hoffset : pointAddArithmeticOffset 2052 = 6164 := rfl
    calc
      pointAddArithmeticOffset 2052 + source <
          6164 + Secp256k1Instance.fieldWidth * 5402 := by
        rw [hoffset]
        exact Nat.add_lt_add_left hsourceUpper 6164
      _ = bitcoinQubitCount := by
        norm_num [bitcoinQubitCount,
          Secp256k1Instance.fieldWidth]
  · simp only [shiftWires, List.mem_map] at hexp
    obtain ⟨source, hsource, rfl⟩ := hexp
    have hsourceUpper := secpLayout_upper source hsource
    have hoffset : pointAddArithmeticOffset 2052 = 6164 := rfl
    calc
      pointAddArithmeticOffset 2052 + source <
          6164 + Secp256k1Instance.fieldWidth * 5402 := by
        rw [hoffset]
        exact Nat.add_lt_add_left hsourceUpper 6164
      _ = bitcoinQubitCount := by
        norm_num [bitcoinQubitCount,
          Secp256k1Instance.fieldWidth]

private theorem bitcoinScalarMulWork_upper :
    ∀ w ∈ scalarMulWork bitcoinWorkStart,
      w < bitcoinQubitCount := by
  intro w hw
  change w ∈ List.range' 1026 pointWidth ++
    controlledPointAddOutWork 1539 at hw
  rcases List.mem_append.mp hw with htemp | hw
  · have hbound := List.mem_range'_1.mp htemp
    calc
      w < 1026 + pointWidth := hbound.2
      _ < bitcoinQubitCount := by
        norm_num [pointWidth, bitcoinQubitCount]
  · change w ∈ List.range' 1539 pointWidth ++
      pointAddWork 2052 at hw
    rcases List.mem_append.mp hw with hchoice | hw
    · have hbound := List.mem_range'_1.mp hchoice
      calc
        w < 1539 + pointWidth := hbound.2
        _ < bitcoinQubitCount := by
          norm_num [pointWidth, bitcoinQubitCount]
    · change w ∈ List.range' 2052 4112 ++
        pointAddArithmeticWork 2052 at hw
      rcases List.mem_append.mp hw with hlocal | harithmetic
      · have hbound := List.mem_range'_1.mp hlocal
        calc
          w < 2052 + 4112 := hbound.2
          _ < bitcoinQubitCount := by
            norm_num [bitcoinQubitCount]
      · exact pointAddArithmeticWork_upper w harithmetic

/--
The fixed submission layout has the required widths, pairwise-disjoint public
and workspace wires, and a fresh QFT ancilla.  The proof uses interval bounds;
it does not evaluate the large workspace with `decide`.
-/
theorem bitcoinWireLayout :
    bitcoinAReg.length = 256 ∧
    bitcoinBReg.length = 256 ∧
    bitcoinPointReg.length = pointWidth ∧
    (bitcoinAReg ++ bitcoinBReg ++ bitcoinPointReg ++
      scalarMulWork bitcoinWorkStart).Nodup ∧
    bitcoinQFTAncilla ∉
      bitcoinAReg ++ bitcoinBReg ++ bitcoinPointReg ++
        scalarMulWork bitcoinWorkStart := by
  have append_nodup_of_bounds :
      ∀ (left right : List Wire) (boundary : Wire),
        left.Nodup →
        right.Nodup →
        (∀ w ∈ left, w < boundary) →
        (∀ w ∈ right, boundary ≤ w) →
        (left ++ right).Nodup := by
    intro left right boundary hleft hright hleftBound hrightBound
    rw [List.nodup_append]
    refine ⟨hleft, hright, ?_⟩
    intro w hwLeft _ hwRight rfl
    exact (Nat.not_lt_of_ge (hrightBound w hwRight)) (hleftBound w hwLeft)

  have hArithmeticNodup :
      (pointAddArithmeticWork 2052).Nodup := by
    exact List.nodup_dedup _
  have hArithmeticOffset : pointAddArithmeticOffset 2052 = 6164 := by
    rfl
  have hArithmeticLower :
      ∀ w ∈ pointAddArithmeticWork 2052, 6164 ≤ w := by
    intro w hw
    simp only [pointAddArithmeticWork, List.mem_dedup,
      List.mem_append] at hw
    rcases hw with (hw | hw) | hw
    all_goals
      simp only [shiftWires, List.mem_map] at hw
      obtain ⟨source, _, rfl⟩ := hw
      rw [hArithmeticOffset]
      exact Nat.le_add_right 6164 source

  have hPointWorkNodup : (pointAddWork 2052).Nodup := by
    change
      (List.range' 2052 4112 ++ pointAddArithmeticWork 2052).Nodup
    apply append_nodup_of_bounds _ _ 6164
    · exact List.nodup_range'
    · exact hArithmeticNodup
    · intro w hw
      exact (List.mem_range'_1.mp hw).2
    · exact hArithmeticLower
  have hPointWorkLower : ∀ w ∈ pointAddWork 2052, 2052 ≤ w := by
    intro w hw
    change
      w ∈ List.range' 2052 4112 ++ pointAddArithmeticWork 2052 at hw
    rcases List.mem_append.mp hw with hw | hw
    · exact (List.mem_range'_1.mp hw).1
    · exact (Nat.le_trans (by norm_num) (hArithmeticLower w hw))

  have hOutWorkNodup : (controlledPointAddOutWork 1539).Nodup := by
    change
      (List.range' 1539 pointWidth ++ pointAddWork 2052).Nodup
    apply append_nodup_of_bounds _ _ 2052
    · exact List.nodup_range'
    · exact hPointWorkNodup
    · intro w hw
      simpa [pointWidth] using (List.mem_range'_1.mp hw).2
    · exact hPointWorkLower
  have hOutWorkLower :
      ∀ w ∈ controlledPointAddOutWork 1539, 1539 ≤ w := by
    intro w hw
    change w ∈ List.range' 1539 pointWidth ++ pointAddWork 2052 at hw
    rcases List.mem_append.mp hw with hw | hw
    · exact (List.mem_range'_1.mp hw).1
    · exact (Nat.le_trans (by norm_num) (hPointWorkLower w hw))

  have hWorkNodup : (scalarMulWork bitcoinWorkStart).Nodup := by
    change
      (List.range' 1026 pointWidth ++
        controlledPointAddOutWork 1539).Nodup
    apply append_nodup_of_bounds _ _ 1539
    · exact List.nodup_range'
    · exact hOutWorkNodup
    · intro w hw
      simpa [pointWidth] using (List.mem_range'_1.mp hw).2
    · exact hOutWorkLower
  have hWorkLower :
      ∀ w ∈ scalarMulWork bitcoinWorkStart, 1026 ≤ w := by
    intro w hw
    change
      w ∈ List.range' 1026 pointWidth ++
        controlledPointAddOutWork 1539 at hw
    rcases List.mem_append.mp hw with hw | hw
    · exact (List.mem_range'_1.mp hw).1
    · exact (Nat.le_trans (by norm_num) (hOutWorkLower w hw))

  have hPublicNodup :
      (bitcoinAReg ++ bitcoinBReg ++ bitcoinPointReg).Nodup := by
    have hab : (bitcoinAReg ++ bitcoinBReg).Nodup := by
      apply append_nodup_of_bounds _ _ 256
      · exact List.nodup_range'
      · exact List.nodup_range'
      · intro w hw
        change w ∈ List.range' 0 256 at hw
        exact (List.mem_range'_1.mp hw).2
      · intro w hw
        change w ∈ List.range' 256 256 at hw
        exact (List.mem_range'_1.mp hw).1
    have habp :
        ((bitcoinAReg ++ bitcoinBReg) ++ bitcoinPointReg).Nodup := by
      apply append_nodup_of_bounds _ _ 512
      · exact hab
      · exact List.nodup_range'
      · intro w hw
        rcases List.mem_append.mp hw with hw | hw
        · change w ∈ List.range' 0 256 at hw
          exact (List.mem_range'_1.mp hw).2.trans_le (by norm_num)
        · change w ∈ List.range' 256 256 at hw
          simpa using (List.mem_range'_1.mp hw).2
      · intro w hw
        change w ∈ List.range' 512 pointWidth at hw
        exact (List.mem_range'_1.mp hw).1
    simpa only [List.append_assoc] using habp
  have hPublicUpper :
      ∀ w ∈ bitcoinAReg ++ bitcoinBReg ++ bitcoinPointReg, w < 1025 := by
    intro w hw
    simp only [List.mem_append] at hw
    rcases hw with hw | hw
    · rcases hw with hw | hw
      · change w ∈ List.range' 0 256 at hw
        exact (List.mem_range'_1.mp hw).2.trans_le (by norm_num)
      · change w ∈ List.range' 256 256 at hw
        exact (List.mem_range'_1.mp hw).2.trans_le (by norm_num)
    · change w ∈ List.range' 512 pointWidth at hw
      simpa [pointWidth] using (List.mem_range'_1.mp hw).2
  have hnodup :
      (bitcoinAReg ++ bitcoinBReg ++ bitcoinPointReg ++
        scalarMulWork bitcoinWorkStart).Nodup := by
    have h := append_nodup_of_bounds
      (bitcoinAReg ++ bitcoinBReg ++ bitcoinPointReg)
      (scalarMulWork bitcoinWorkStart) 1026
      hPublicNodup hWorkNodup
      (fun w hw => (hPublicUpper w hw).trans (by norm_num)) hWorkLower
    simpa only [List.append_assoc] using h
  have hancillaFresh :
      bitcoinQFTAncilla ∉
        bitcoinAReg ++ bitcoinBReg ++ bitcoinPointReg ++
          scalarMulWork bitcoinWorkStart := by
    intro hw
    have hw' :
        bitcoinQFTAncilla ∈
          (bitcoinAReg ++ bitcoinBReg ++ bitcoinPointReg) ++
            scalarMulWork bitcoinWorkStart := by
      simpa only [List.append_assoc] using hw
    rcases List.mem_append.mp hw' with hwPublic | hwWork
    · have := hPublicUpper bitcoinQFTAncilla hwPublic
      norm_num [bitcoinQFTAncilla] at this
    · have := hWorkLower bitcoinQFTAncilla hwWork
      norm_num [bitcoinQFTAncilla] at this

  exact ⟨by simp [bitcoinAReg], by simp [bitcoinBReg],
    by simp [bitcoinPointReg], hnodup, hancillaFresh⟩

private theorem bitcoinDeclaredWires_subset :
    ∀ w ∈
      bitcoinAReg ++ bitcoinBReg ++ bitcoinPointReg ++
        scalarMulWork bitcoinWorkStart ++ [bitcoinQFTAncilla],
      w ∈ bitcoinAllWires := by
  intro w hw
  simp only [List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hw
  rcases hw with (((ha | hb) | hpoint) | hwork) | hancilla
  · change w ∈ List.range' 0 256 at ha
    have hbound := (List.mem_range'_1.mp ha).2
    simpa [bitcoinAllWires, bitcoinQubitCount] using
      (hbound.trans (by norm_num : 256 < 1394478))
  · change w ∈ List.range' 256 256 at hb
    have hbound := (List.mem_range'_1.mp hb).2
    simpa [bitcoinAllWires, bitcoinQubitCount] using
      (hbound.trans (by norm_num : 512 < 1394478))
  · change w ∈ List.range' 512 pointWidth at hpoint
    have hbound := (List.mem_range'_1.mp hpoint).2
    have hlt : w < bitcoinQubitCount := by
      exact hbound.trans (by
        norm_num [pointWidth, bitcoinQubitCount])
    simpa [bitcoinAllWires] using hlt
  · have hlt := bitcoinScalarMulWork_upper w hwork
    simpa [bitcoinAllWires] using hlt
  · subst w
    simp [bitcoinAllWires, bitcoinQubitCount,
      bitcoinQFTAncilla]

private theorem qubitCount_le_of_usesOnly
    {support : List Wire} {c : Circuit}
    (hsupport : support.Nodup)
    (huses : CircuitUsesOnly support c) :
    qubitCount c ≤ support.length := by
  have hsubset :
      (circuitWires c).dedup.toFinset ⊆ support.toFinset := by
    intro w hw
    have hwDedup : w ∈ (circuitWires c).dedup := by
      simpa using hw
    have hwCircuit : w ∈ circuitWires c := by
      simpa using hwDedup
    have hwSupport :=
      (ModAddSupport.circuitUsesOnly_iff_support support c).mp
        huses w hwCircuit
    simpa using hwSupport
  have hcard := Finset.card_le_card hsubset
  rw [List.toFinset_card_of_nodup (List.nodup_dedup _),
    List.toFinset_card_of_nodup hsupport] at hcard
  simpa [qubitCount] using hcard

/-- The current concrete one-trial Bitcoin circuit touches at most
`1,394,478` distinct qubit wires.  Sequential measured repetition reuses this
same device, so the bound is not multiplied by 26. -/
theorem bitcoinECDLPTrial_qubitCount
    (Q : Point) :
    qubitCount
      (ecdlpTrial bitcoinAReg bitcoinBReg bitcoinPointReg
        bitcoinWorkStart bitcoinQFTAncilla Q) ≤
      bitcoinQubitCount := by
  have hnodup : bitcoinAllWires.Nodup := by
    rw [bitcoinAllWires]
    exact List.nodup_range
  have huses : CircuitUsesOnly bitcoinAllWires
      (ecdlpTrial bitcoinAReg bitcoinBReg bitcoinPointReg
        bitcoinWorkStart bitcoinQFTAncilla Q) := by
    apply Arithmetic.usesOnly_mono
      (ecdlpTrial_usesOnly Q
        bitcoinAReg bitcoinBReg bitcoinPointReg
        bitcoinWorkStart bitcoinQFTAncilla)
    exact bitcoinDeclaredWires_subset
  have hbound := qubitCount_le_of_usesOnly hnodup huses
  rw [bitcoinAllWires_length] at hbound
  exact hbound

/-- The exact aggregate T-count of the concrete repeated Bitcoin procedure. -/
def bitcoinECDLPTotalGateCount : Nat :=
  21888426033809920

/-- Repeating the exact trial 26 times has T-count `21888426033809920`. -/
theorem bitcoinECDLPTotalGateCount_correct
    (aReg bReg pointReg : List Wire)
    (workStart qftAncilla : Wire)
    (haLength : aReg.length = 256)
    (hbLength : bReg.length = 256)
    (hpointLength : pointReg.length = pointWidth)
    {d : Nat} (Q : Point)
    (hQ : Q = d • G)
    (hQnonzero : Q ≠ 0) :
    repeatedTCount
      (ecdlpTrial aReg bReg pointReg workStart qftAncilla Q) 26 =
      bitcoinECDLPTotalGateCount := by
  unfold repeatedTCount
  rw [ecdlpTrial_tCount Q aReg bReg pointReg workStart qftAncilla
    haLength hbLength hpointLength hQ hQnonzero]
  norm_num [bitcoinECDLPTotalGateCount]

end Secp256k1
end ShorECDLP
