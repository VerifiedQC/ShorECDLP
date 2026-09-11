#!/usr/bin/env python3
"""Check primitive budgets of the emitted variable modular circuits."""
from pathlib import Path
import subprocess
import tempfile
ROOT = Path(__file__).resolve().parents[1]
LEAN_CHECK = r"""
import ShorECDLP.Submission.«2607_13816».Arithmetic.ModularPrimitiveCounts

open ShorECDLP ShorECDLP.Paper2607_13816 Quantum
def main : IO Unit := do
  let mut checked := 0
  for n in [2:6] do
    let a := List.range' 5 n
    let b := List.range' (5+n) n
    let add := primitiveResources (.unitary (controlledAddCarry b a 0 1 4) .done)
    let sub := primitiveResources (.unitary (controlledSubCarry b a 0 1 4) .done)
    unless add == (⟨0,0,4*n,3*n+1,0,0⟩ : PrimitiveResources) && sub == add do
      throw (IO.userError "coherent carry counts failed")
    let cmp := primitiveResources (.unitary (controlledCompareLT a b 0 1 4) .done)
    unless cmp == (⟨2*n+4,0,4*n,2*n+1,0,0⟩ : PrimitiveResources) do
      throw (IO.userError "coherent comparison counts failed")
    for p in [3:2^n] do
      if p % 2 == 1 then
        let correction := (List.range n).map (fun i => (2^n-p).testBit i)
        let modulus := (List.range n).map (p.testBit)
        for circuit in [controlledModularAdd b a correction p 0 1 2 3 4,
            controlledModularSub b a modulus p 0 1 2 3 4] do
          let v := primitiveResources circuit
          unless v.x≤23*n+1 && v.h≤8*n-4 && v.cnot≤38*n-16 && v.toffoli≤11*n-3 &&
              v.phase==0 && v.measurements≤2*n-1 do
            throw (IO.userError s!"variable budget failed at width {n}, modulus {p}: {repr v}")
          checked := checked+1
        for circuit in [modularDouble a b correction p 1 2 3 4,
            modularHalve a b modulus p 1 2 3 4] do
          let v := primitiveResources circuit
          unless v.x≤21*n-3 && v.h≤8*n-4 && v.cnot≤33*n-16 && v.toffoli≤6*n-5 &&
              v.phase==0 && v.measurements≤2*n-1 do
            throw (IO.userError s!"scaling budget failed at width {n}, modulus {p}: {repr v}")
          checked := checked+1
  IO.println s!"{checked} actual variable/scaling circuits passed primitive bounds"
"""
if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="variable-primitives-") as directory:
        source = Path(directory) / "Check.lean"
        source.write_text(LEAN_CHECK)
        subprocess.run(["lake", "env", "lean", "--run", str(source)], cwd=ROOT, check=True)
