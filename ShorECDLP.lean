-- ShorECDLP: verified end-to-end resource estimate for Shor's algorithm on the
-- elliptic-curve discrete-log problem over secp256k1 (the quantum attack on ECDSA).
--
-- Root aggregator. M0 seeds the instruction set and the Toffoli-caliber cost model;
-- later milestones add field arithmetic (M1), point addition (M2), scalar
-- multiplication + oracle (M3), quantum semantics + end-to-end correctness (M4),
-- and the submission spec (M5).
import ShorECDLP.Framework.InstructionSet
import ShorECDLP.Framework.CostModel
import ShorECDLP.Framework.Contract
import ShorECDLP.Framework.BasisState
import ShorECDLP.Framework.Classical.Semantics
import ShorECDLP.Submission.Field
import ShorECDLP.Submission.QFT.Main
import ShorECDLP.Submission.Arithmetic.Contracts
import ShorECDLP.Submission.Arithmetic.Controlled_PointAdd
import ShorECDLP.Submission.Arithmetic.Adder
import ShorECDLP.Submission.Arithmetic.FermatInv
import ShorECDLP.Submission.Arithmetic.ModAdd
import ShorECDLP.Submission.Arithmetic.ModExp
import ShorECDLP.Submission.Arithmetic.ModMul
import ShorECDLP.Submission.Arithmetic.ModSub
import ShorECDLP.Submission.Arithmetic.PointAdd
import ShorECDLP.Submission.Arithmetic.Predicates
import ShorECDLP.Submission.Arithmetic.Primitives
import ShorECDLP.Submission.Arithmetic.RippleAdder
import ShorECDLP.Submission.Arithmetic.ScalarMul
import ShorECDLP.Submission.Arithmetic.Secp256k1Instance
import ShorECDLP.Submission.EllipticCurve.AffineFormula
import ShorECDLP.Submission.EllipticCurve.ECDLPOracle
import ShorECDLP.Submission.EllipticCurve.Precompute
import ShorECDLP.Submission.EllipticCurve.PointEncoding
import ShorECDLP.Submission.EllipticCurve.PointRegister
import ShorECDLP.Submission.EllipticCurve.Secp256k1
import ShorECDLP.Submission.Correctness.EndToEnd
import ShorECDLP.Submission.Correctness.Reduction
import ShorECDLP.Submission.OrderFinding.OracleSpec
import ShorECDLP.Submission.OrderFinding.OracleRefinement
import ShorECDLP.Submission.OrderFinding.PhaseEstimation.Main
import ShorECDLP.Submission.OrderFinding.Main
