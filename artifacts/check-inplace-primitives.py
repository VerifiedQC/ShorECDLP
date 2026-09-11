#!/usr/bin/env python3
"""Replay reset/correction trees and the fixed Figure 15 gate streams."""
from pathlib import Path
import subprocess
import tempfile
ROOT=Path(__file__).resolve().parents[1]
LEAN_CHECK=r'''
import ShorECDLP.Submission.«2607_13816».Arithmetic.ZeroAllowedPrimitiveCounts
open ShorECDLP ShorECDLP.Paper2607_13816 Quantum
def gateVector : Gate → PrimitiveResources
  | .X _ => ⟨1,0,0,0,0,0⟩
  | .H _ => ⟨0,1,0,0,0,0⟩
  | .CX _ _ => ⟨0,0,1,0,0,0⟩
  | .CCX _ _ _ => ⟨0,0,0,1,0,0⟩
  | .P _ _ _ => ⟨0,0,0,0,1,0⟩
def streamVector (g : Circuit) : PrimitiveResources :=
  g.foldl (fun v g => v.add (gateVector g)) ⟨0,0,0,0,0,0⟩
def emit (kind : String) (n mask : Nat) (v : PrimitiveResources) : IO Unit :=
  IO.println s!"{kind} {n} {mask} {v.x} {v.h} {v.cnot} {v.toffoli} {v.phase} {v.measurements}"
def main : IO Unit := do
  for offset in [0,1000] do
    for n in List.range 9 do
      let targets := List.range' offset n
      for mask in List.range (2^n) do
        let bs := (List.range n).map (Nat.testBit mask)
        emit "correction" n mask (streamVector (registerZCorrection targets bs))
      let p := measureResetThen targets (fun bs => .unitary (registerZCorrection targets bs) .done)
      emit "reset" n 0 (primitiveResources p)
      unless primitiveResources (p.relabel eeaWorkspaceExchange)==primitiveResources p do
        throw (IO.userError "relabel changed actual reset vector")
    for mask in [0,1,2^255,2^256-1,(2^256-1)/3] do
      let bs := (List.range 256).map (Nat.testBit mask)
      emit "correction" 256 mask (streamVector (registerZCorrection (List.range' offset 256) bs))
  for (g,i) in [fig15SwapOutput,fig15ZeroPrepare,fig15ZeroRestore].zipIdx do
    emit "fixed" i 0 (streamVector g)
'''
if __name__=='__main__':
    with tempfile.TemporaryDirectory(prefix='inplace-primitives-') as directory:
        source=Path(directory)/'Check.lean';source.write_text(LEAN_CHECK)
        out=subprocess.check_output(['lake','env','lean','--run',str(source)],cwd=ROOT,text=True)
    counts={'correction':0,'reset':0,'fixed':0}
    for line in out.splitlines():
        kind,n,mask,*fields=line.split();n=int(n);mask=int(mask);v=list(map(int,fields))
        if kind=='correction':
            ones=bin(mask%(2**n)).count('1');want=[ones,2*ones,0,0,0,0]
        elif kind=='reset': want=[n,2*n,0,0,0,n]
        else: want=[[0,0,768,0,0,0],[512,0,1,509,0,0],[512,0,1,509,0,0]][n]
        assert v==want,(kind,n,mask,v,want)
        counts[kind]+=1
    assert counts=={'correction':1032,'reset':18,'fixed':3},counts
    print('1,032 correction streams, 18 full reset trees with relabeling, and 3 fixed production streams passed')
