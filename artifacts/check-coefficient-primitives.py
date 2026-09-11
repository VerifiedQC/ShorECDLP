#!/usr/bin/env python3
"""Check exact primitive vectors of both coefficient-prefix directions."""
from pathlib import Path
import subprocess
import tempfile
ROOT=Path(__file__).resolve().parents[1]
LEAN_CHECK=r"""
import ShorECDLP.Submission.«2607_13816».EEA.CoefficientPrimitiveCounts
open ShorECDLP ShorECDLP.Paper2607_13816 Quantum

def regs (k K : Nat) : CoefficientPrefixRegisters :=
  ⟨0,1,List.range' 2 (K-k+1),List.range' 10 (K-k+1),List.range' 20 3,List.range' 30 6⟩
def main : IO Unit := do
  let mut checked := 0
  for (k,K) in [(0,0),(0,1),(1,2)] do
    let r := regs k K
    let tree := coefficientPrefixTree r k K
    for mode in [RippleMode.add,RippleMode.sub] do
      for signUpdate in [false,true] do
        for target in [CoefficientTarget.work1,CoefficientTarget.work2] do
          for inverse in [false,true] do
            let program := if inverse then coefficientPrefixInverseAdaptive else coefficientPrefixAdaptive
            let actual := primitiveResources (program r k K mode signUpdate target)
            let expected : PrimitiveResources :=
              ⟨8*tree.internalNodes,4*tree.leaves+4*tree.internalNodes,
               2+8*tree.leaves+6*tree.internalNodes+(if signUpdate then 1 else 0),
               5*tree.leaves+2*tree.internalNodes,0,2*tree.leaves+2*tree.internalNodes⟩
            unless actual == expected do throw (IO.userError "coefficient primitive mismatch")
            checked := checked+1
  IO.println s!"{checked} actual coefficient prefixes passed exact primitive vectors"

"""
if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="coefficient-primitives-") as directory:
        source=Path(directory)/"Check.lean"
        source.write_text(LEAN_CHECK)
        subprocess.run(["lake","env","lean","--run",str(source)],cwd=ROOT,check=True)
