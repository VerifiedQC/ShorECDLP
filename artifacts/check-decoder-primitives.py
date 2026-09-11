#!/usr/bin/env python3
"""Replay primitive counts for both orders of unary and paired decoders."""
from pathlib import Path
import subprocess
import tempfile
ROOT = Path(__file__).resolve().parents[1]
LEAN_CHECK = r"""
import ShorECDLP.Submission.«2607_13816».EEA.DecoderPrimitiveCounts
open ShorECDLP ShorECDLP.Paper2607_13816 Quantum

def oneTree : Nat → UnaryActionTree
  | 0 => .leaf 0
  | n+1 => .node (10+n) (oneTree n) (.leaf (n+1))
def twoTree : Nat → DualUnaryActionTree
  | 0 => .leaf 0
  | n+1 => .node (10+n) (30+n) (twoTree n) (.leaf (n+1))
def main : IO Unit := do
  let mut checked := 0
  for n in [0:5] do
    for order in [UnaryOrder.inc,UnaryOrder.dec] do
      for adaptive in [false,true] do
        let leaf := fun (_ : Nat) (q : Wire) =>
          if adaptive then .xMeasureReset 100 .done (.unitary [.H 101,.P .forward 2 102] .done)
          else .unitary [.X q,.CX q 101] .done
        let v := primitiveResources (leaf 0 0)
        let one := primitiveResources (unaryAdaptiveAction order leaf (oneTree n) 0 (List.range' 50 n))
        let two := primitiveResources (dualUnaryAdaptiveAction order (fun l a _ => leaf l a)
          (twoTree n) 0 1 (List.range' 50 n) (List.range' 70 n))
        unless one == (⟨v.x*(n+1)+4*n,v.h*(n+1)+2*n,v.cnot*(n+1)+3*n,
            v.toffoli*(n+1)+n,v.phase*(n+1),v.measurements*(n+1)+n⟩ : PrimitiveResources) do
          throw (IO.userError "unary decoder primitive mismatch")
        unless two == (⟨v.x*(n+1)+8*n,v.h*(n+1)+4*n,v.cnot*(n+1)+6*n,
            v.toffoli*(n+1)+2*n,v.phase*(n+1),v.measurements*(n+1)+2*n⟩ : PrimitiveResources) do
          throw (IO.userError "paired decoder primitive mismatch")
        checked := checked+2
  IO.println s!"{checked} actual unary/paired decoder trees passed primitive formulas"
"""
if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="decoder-primitives-") as directory:
        source = Path(directory) / "Check.lean"
        source.write_text(LEAN_CHECK)
        subprocess.run(["lake","env","lean","--run",str(source)],cwd=ROOT,check=True)
