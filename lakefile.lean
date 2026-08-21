import Lake
open Lake DSL

package «ShorECDLP» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

-- Mathlib is pinned via the committed `lake-manifest.json` to the same revision as
-- VerifiedQC/ForShor (lean4:v4.28.0), so the two developments share a known-good
-- toolchain/Mathlib pairing.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «ShorECDLP» where
  -- add any library configuration options here
