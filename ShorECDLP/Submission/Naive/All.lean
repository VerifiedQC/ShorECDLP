import ShorECDLP.Submission.Naive.Arithmetic.Contracts
import ShorECDLP.Submission.Naive.Arithmetic.Controlled_PointAdd
import ShorECDLP.Submission.Naive.Arithmetic.Adder
import ShorECDLP.Submission.Naive.Arithmetic.FermatInv
import ShorECDLP.Submission.Naive.Arithmetic.ModAdd
import ShorECDLP.Submission.Naive.Arithmetic.ModExp
import ShorECDLP.Submission.Naive.Arithmetic.ModMul
import ShorECDLP.Submission.Naive.Arithmetic.ModSub
import ShorECDLP.Submission.Naive.Arithmetic.PointAdd
import ShorECDLP.Submission.Naive.Arithmetic.Predicates
import ShorECDLP.Submission.Naive.Arithmetic.Primitives
import ShorECDLP.Submission.Naive.Arithmetic.RippleAdder
import ShorECDLP.Submission.Naive.Arithmetic.ScalarMul
import ShorECDLP.Submission.Naive.Arithmetic.Secp256k1Instance
import ShorECDLP.Submission.Naive.Contract
import ShorECDLP.Submission.Naive.Correctness.EndToEnd
import ShorECDLP.Submission.Naive.Correctness.Trial
import ShorECDLP.Submission.Naive.EllipticCurve.ECDLPOracle
import ShorECDLP.Submission.Naive.EllipticCurve.PointEncoding
import ShorECDLP.Submission.Naive.EllipticCurve.PointRegister
import ShorECDLP.Submission.Naive.EllipticCurve.Secp256k1
import ShorECDLP.Submission.Naive.OrderFinding.OracleSpec
import ShorECDLP.Submission.Naive.OrderFinding.OracleRefinement
import ShorECDLP.Submission.Naive.OrderFinding.PhaseEstimation.Main
import ShorECDLP.Submission.Naive.OrderFinding.Main
import ShorECDLP.Submission.Naive.QFT.Main
import ShorECDLP.Submission.Naive.Submission

/-!
# Naive verified submission

Root-closure aggregator for the existing unitary, binary-double-and-add Bitcoin ECDLP
submission. Declaration namespaces are intentionally unchanged by the source relocation.
-/
