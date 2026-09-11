#!/usr/bin/env python3
"""Check emitted ripple leaves and production-width extremal measurement paths."""
from pathlib import Path
import subprocess
import tempfile
ROOT=Path(__file__).resolve().parents[1]
LEAN_CHECK=r"""
import ShorECDLP.Submission.«2607_13816».EEA.RipplePrimitiveCounts
open ShorECDLP ShorECDLP.Paper2607_13816 Quantum

def gateVector : Gate → PrimitiveResources
  | .X _ => ⟨1,0,0,0,0,0⟩
  | .H _ => ⟨0,1,0,0,0,0⟩
  | .CX _ _ => ⟨0,0,1,0,0,0⟩
  | .CCX _ _ _ => ⟨0,0,0,1,0,0⟩
  | .P _ _ _ => ⟨0,0,0,0,1,0⟩
def pathVector (outcome : Bool) : AdaptiveCircuit → PrimitiveResources
  | .done => ⟨0,0,0,0,0,0⟩
  | .unitary g next => (g.foldl (fun (v : PrimitiveResources) gate => v.add (gateVector gate)) ⟨0,0,0,0,0,0⟩).add (pathVector outcome next)
  | .xMeasureReset _ l r => (⟨0,0,0,0,0,1⟩ : PrimitiveResources).add
      (if outcome then pathVector outcome r else pathVector outcome l)
def main : IO Unit := do
  let mut checked := 0
  for mode in [RippleMode.add,RippleMode.sub] do
    for special in [false,true] do
      for label in [0:4] do
        let masked := special && label==0
        let first := intervalFirstLeafAdaptive mode special 0 1 2 3 4 5 6 label 7 8
        let second := intervalSecondLeafAdaptive mode special 0 1 2 3 4 5 6 label 7 8
        for (c,ccx) in [(first,if mode==.add then 2 else 3),(second,if mode==.add then 3 else 2)] do
          unless primitiveResources c == (⟨if masked then 4 else 0,2,if masked then 3 else 5,
              ccx+(if masked then 2 else 0),0,1⟩ : PrimitiveResources) do
            throw (IO.userError "main ripple leaf mismatch")
          checked := checked+1
    for value in [0,1,255,256,511] do
      let zeros := ((List.range 9).filter (fun i => !(value.testBit i))).length
      let right := List.range' 10 9
      let left := List.range' 20 9
      let scratches := List.range' 30 7
      let first := topSpecialFirstLeafAdaptive mode value right left 0 1 2 3 4 5 scratches 6 7
      let second := topSpecialSecondLeafAdaptive mode value right left 0 1 2 3 4 5 scratches 6 7
      for (c,ccx) in [(first,if mode==.add then 36 else 37),(second,if mode==.add then 37 else 36)] do
        unless pathVector true c == (⟨8*zeros,58,31,ccx,0,29⟩ : PrimitiveResources) do
          throw (IO.userError "top ripple extremal path mismatch")
        unless pathVector false c == (⟨8*zeros,0,2,ccx,0,29⟩ : PrimitiveResources) do
          throw (IO.userError "top ripple zero-outcome path mismatch")
        checked := checked+1
  IO.println s!"{checked} main/top ripple leaf checks passed, including 9-bit extremal paths"
"""
if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="ripple-primitives-") as directory:
        source=Path(directory)/"Check.lean"
        source.write_text(LEAN_CHECK)
        subprocess.run(["lake","env","lean","--run",str(source)],cwd=ROOT,check=True)
