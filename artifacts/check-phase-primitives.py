#!/usr/bin/env python3
"""Check phase update primitive vectors and production-width test components."""
from pathlib import Path
import subprocess
import tempfile
ROOT=Path(__file__).resolve().parents[1]
LEAN_CHECK=r"""
import ShorECDLP.Submission.«2607_13816».EEA.PhasePrimitiveCounts
open ShorECDLP ShorECDLP.Paper2607_13816 Quantum

def regs (n : Nat) : PhaseUpdateRegisters :=
  ⟨0,1,2,List.range' 10 n,List.range' 20 n,List.range' 30 n,3,4,5,6,7,List.range' 40 (n+1)⟩
def main : IO Unit := do
  let mut checked := 0
  for n in [0:4] do
    let r := regs n
    for inverse in [false,true] do
      let c := if inverse then phaseUpdateEpochInverseAdaptive r 8 else phaseUpdateEpochAdaptive r 8
      let m := 2*(2*(n-2)+(n-1))
      let expected : PrimitiveResources :=
        ⟨8+(if n==0 then 4 else 0),2*m,
          6+2*(2*((if n==1 then 1 else 0)+(n-2))+(if n==0 then 1 else 0)+(n-1)),
          4+2*(2*(n-1)+n),0,m⟩
      unless primitiveResources c == expected do throw (IO.userError "phase update primitive mismatch")
      checked := checked+1
  let r := regs 9
  let q := primitiveResources (mcxVChainAdaptive r.lengthQ r.zeroQ r.equalityScratch)
  let rp := primitiveResources (mcxVChainAdaptive r.lengthRPrime r.zeroRPrime r.equalityScratch)
  let sh := primitiveResources (mcxVChainAdaptive (r.lengthS++[8]) r.zeroS r.equalityScratch)
  let tests := q.add (rp.add sh)
  unless tests.add (tests.add ⟨8,0,6,4,0,0⟩) == (⟨8,88,50,54,0,44⟩ : PrimitiveResources) do
    throw (IO.userError "production phase components mismatch")
  IO.println s!"{checked} small complete phase updates and production 9/9/10-bit components passed"

"""
if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="phase-primitives-") as directory:
        source=Path(directory)/"Check.lean"
        source.write_text(LEAN_CHECK)
        subprocess.run(["lake","env","lean","--run",str(source)],cwd=ROOT,check=True)
