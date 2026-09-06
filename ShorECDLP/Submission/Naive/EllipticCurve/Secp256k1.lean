import ShorECDLP.Math.BitcoinCurve

/-!
# secp256k1 compatibility import

The fixed curve, point type, and standard generator are part of the Bitcoin
problem and therefore live in `Math.BitcoinCurve`. This module keeps a Naive-submission
compatibility import available to downstream implementation files without redefining or
wrapping those mathematical objects.
-/
