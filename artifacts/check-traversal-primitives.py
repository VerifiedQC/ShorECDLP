#!/usr/bin/env python3
"""Replay exact primitive formulas for both main EEA traversals."""
from pathlib import Path
import subprocess
import tempfile
ROOT = Path(__file__).resolve().parents[1]
LEAN_CHECK = r"""
import ShorECDLP.Submission.«2607_13816».EEA.TraversalPrimitiveCounts
open ShorECDLP ShorECDLP.Paper2607_13816 Quantum
def twoTree : Nat → DualUnaryActionTree
  | 0 => .leaf 0
  | n+1 => .node (10+n) (30+n) (twoTree n) (.leaf (n+1))
def main : IO Unit := do
  let mut checked := 0
  for n in [0:4] do
    for mode in [RippleMode.add,RippleMode.sub] do
      for special in [false,true] do
        for second in [false,true] do
          let program := if second then intervalSecondTraversalAdaptive else intervalFirstTraversalAdaptive
          let v := primitiveResources (program mode special 100 101 102 103 104
            (fun l => 200+l) (fun l => 300+l) (twoTree n) 0 1 (List.range' 50 n) (List.range' 70 n))
          let labels := List.range (n+1)
          let cell := (if second then rippleSecondCellToffoliCost mode else rippleFirstCellToffoliCost mode)-1
          let expected : PrimitiveResources :=
            ⟨(labels.map (fun l => if maskedZeroLeaf special l then 4 else 0)).sum+8*n,
             2*(n+1)+4*n,
             (labels.map (fun l => if maskedZeroLeaf special l then 3 else 5)).sum+6*n,
             (labels.map (fun l => cell+(if maskedZeroLeaf special l then 2 else 0))).sum+2*n,
             0,n+1+2*n⟩
          unless v == expected do throw (IO.userError "traversal primitive mismatch")
          checked := checked+1
  IO.println s!"{checked} actual EEA traversals passed primitive formulas"
"""
if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="traversal-primitives-") as directory:
        source = Path(directory) / "Check.lean"
        source.write_text(LEAN_CHECK)
        subprocess.run(["lake","env","lean","--run",str(source)],cwd=ROOT,check=True)
