import ShorECDLP.Framework.BitcoinCurve

/-!
# secp256k1 compatibility import

The fixed curve, point type, and standard generator are part of the Bitcoin
problem and therefore live in `Framework.BitcoinCurve`.  This module keeps the
established Submission import path available to downstream implementation
files without redefining or wrapping those mathematical objects.
-/
