import ShorECDLP.Math.Bitcoin
import ShorECDLP.Math.BitcoinCurve
import ShorECDLP.Math.BitcoinPrimes
import ShorECDLP.Math.Field
import ShorECDLP.Math.Correctness.Reduction
import ShorECDLP.Math.EllipticCurve.AffineFormula
import ShorECDLP.Math.EllipticCurve.GeneratorOrder
import ShorECDLP.Math.EllipticCurve.Precompute

/-!
# Shared mathematical layer

This aggregator exposes the problem-specific definitions and pure lemmas shared by
independent submissions. Every transitive project dependency of this directory stays
inside `ShorECDLP.Math`; the source verifier enforces that boundary.
-/
