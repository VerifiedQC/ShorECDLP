#!/usr/bin/env python3
"""Replay each emitted length-table row and each fixed wrapper gate stream."""
from pathlib import Path
import subprocess
import tempfile
ROOT=Path(__file__).resolve().parents[1]
LEAN_CHECK=r'''
import ShorECDLP.Submission.«2607_13816».EEA.AdaptiveWrapper
import ShorECDLP.Submission.«2607_13816».Arithmetic.UnitaryPrimitiveCounts
open ShorECDLP ShorECDLP.Paper2607_13816 Quantum
def gateVector : Gate → PrimitiveResources
  | .X _ => ⟨1,0,0,0,0,0⟩
  | .H _ => ⟨0,1,0,0,0,0⟩
  | .CX _ _ => ⟨0,0,1,0,0,0⟩
  | .CCX _ _ _ => ⟨0,0,0,1,0,0⟩
  | .P _ _ _ => ⟨0,0,0,0,1,0⟩
def streamVector (g : Circuit) : PrimitiveResources :=
  g.foldl (fun v g => v.add (gateVector g)) ⟨0,0,0,0,0,0⟩
def emit (kind : String) (index : Nat) (v : PrimitiveResources) : IO Unit :=
  IO.println s!"{kind} {index} {v.x} {v.h} {v.cnot} {v.toffoli} {v.phase} {v.measurements}"
def main : IO Unit := do
  for offset in [0,1000] do
    let input := List.range' (offset+266) 256
    let targets := List.range' (offset+549) 9
    let scratch := (List.range' (offset+7) 256).reverse.take 254
    let mut total : PrimitiveResources := ⟨0,0,0,0,0,0⟩
    for (row,index) in (lengthInitializeCases input 9).zipIdx do
      let actual := streamVector (lengthInitializeCase row.1 row.2.1 targets row.2.2 (offset+558) scratch (2^256-2^32-977))
      emit "row" index actual
      total := total.add actual
    emit "total" offset total
  for (g,index) in [workRegistersPrepare,workRegistersRestore,canonicalWork2Rotation,
      canonicalWork2InverseRotation,terminalEpochCompression,terminalWork1Clear].zipIdx do
    emit "fixed" index (streamVector g)
'''
if __name__ == '__main__':
    with tempfile.TemporaryDirectory(prefix='wrapper-primitives-') as directory:
        source=Path(directory)/'Check.lean'; source.write_text(LEAN_CHECK)
        out=subprocess.check_output(['lake','env','lean','--run',str(source)],cwd=ROOT,text=True)
    p=2**256-2**32-977
    pop=lambda n: bin(n).count('1')
    expected=[]
    # Source first-one rows inspect prefixes 1..256; final all-zero row uses all 256 bits.
    for first in range(256):
        controls=first+1
        encoded=255-first
        expected.append([4*first+4*pop(p%(2**254)),0,2*(1 if controls==1 else 0)+pop(encoded%512),2*(0 if controls<2 else 2*controls-3),0,0])
    expected.append([4*256+4*pop(p%(2**254)),0,pop(511),2*(2*256-3),0,0])
    fixed=[[251,0,390,0,0,0],[251,0,390,0,0,0],[6,0,5240,2620,0,0],[6,0,5240,2620,0,0],[10,0,0,15,0,0],[251,0,0,0,0,0]]
    checked=0
    for line in out.splitlines():
        kind,idx,*values=line.split(); idx=int(idx); values=list(map(int,values))
        wanted=expected[idx] if kind=='row' else fixed[idx] if kind=='fixed' else [386528,0,1035,131068,0,0]
        assert values==wanted,(kind,idx,values,wanted)
        checked+=1
    assert checked==522,checked
    print('514 production length rows, two totals and six fixed streams passed')
