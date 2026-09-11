#!/usr/bin/env python3
"""Check exact primitive formulas for measured equality selectors."""
from pathlib import Path
import subprocess
import tempfile
ROOT=Path(__file__).resolve().parents[1]
LEAN_CHECK=r"""
import ShorECDLP.Submission.«2607_13816».EEA.SelectorPrimitiveCounts
open ShorECDLP ShorECDLP.Paper2607_13816 Quantum
def main : IO Unit := do
  let mut checked := 0
  for n in [0:7] do
    let reg := List.range' 3 n
    let scratch := List.range' (3+n) (n-2)
    let chain := primitiveResources (mcxVChainAdaptive reg 2 scratch)
    unless chain == (⟨if n==0 then 1 else 0,2*(n-2),(if n==1 then 1 else 0)+(n-2),n-1,0,n-2⟩ : PrimitiveResources) do
      throw (IO.userError "MCX primitive mismatch")
    for k in [0:2^n+1] do
      let zeros := ((List.range n).filter (fun i => !(k.testBit i))).length
      let v := primitiveResources (computeEqConstAdaptive reg k 2 scratch)
      let u := primitiveResources (toggleEqConstUnderControlAdaptive 0 reg k 1 2 scratch)
      let x := 2*zeros+(if n==0 then 1 else 0)
      unless v == (⟨x,2*(n-2),(if n==1 then 1 else 0)+(n-2),n-1,0,n-2⟩ : PrimitiveResources) do
        throw (IO.userError s!"equality primitive mismatch {n}/{k}")
      unless u == (⟨2*x,4*(n-2),2*((if n==1 then 1 else 0)+(n-2)),2*(n-1)+1,0,2*(n-2)⟩ : PrimitiveResources) do
        throw (IO.userError s!"controlled equality primitive mismatch {n}/{k}")
      checked := checked+2
  IO.println s!"{checked} actual equality selectors and seven v-chains passed exact primitive formulas"
"""
if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="selector-primitives-") as directory:
        source=Path(directory)/"Check.lean"
        source.write_text(LEAN_CHECK)
        subprocess.run(["lake","env","lean","--run",str(source)],cwd=ROOT,check=True)
