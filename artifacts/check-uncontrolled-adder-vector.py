#!/usr/bin/env python3
"""Replay actual small constant-adder measurement trees for exact vectors after fixed-control compilation."""
from pathlib import Path
import subprocess
import tempfile
ROOT=Path(__file__).resolve().parents[1]
LEAN_CHECK=r'''
import ShorECDLP.Submission.«2607_13816».Arithmetic.UncontrolledAdd
open ShorECDLP ShorECDLP.Paper2607_13816
def main : IO Unit := do
  for offset in [0,100] do
    for n in List.range 7 do
      for k in List.range (2^n) do
        let input := List.range' (offset+10) n
        let dirty := List.range' (offset+20) (n-1)
        let bs := (List.range n).map (Nat.testBit k)
        let actual := gidneyAddConst input dirty bs (offset+1) (offset+2) (offset+3)
        let lowered := constantControlProgram offset (controlledGidneyAddConst input dirty bs offset (offset+1) (offset+2) (offset+3))
        let v := primitiveResources actual
        unless v==primitiveResources lowered do
          throw (IO.userError "virtual-control choice changed counts")
        IO.println s!"{n} {k} {v.x} {v.h} {v.cnot} {v.toffoli} {v.phase} {v.measurements}"
'''
def main():
    with tempfile.TemporaryDirectory(prefix='gidney-add-exact-') as tmp:
        p=Path(tmp)/'Main.lean';p.write_text(LEAN_CHECK)
        result=subprocess.run(['lake','env','lean','--run',str(p)],cwd=ROOT,text=True,capture_output=True,check=True)
    checks=0
    for line in result.stdout.splitlines():
        n,k,x,h,cx,ccx,p,m=map(int,line.split())
        interior=bin((k>>1)&((1<<max(n-2,0))-1)).count('1')
        first=k&1
        last=(k>>(n-1))&1 if n else 0
        expected=(4*n-2+8*first+10*interior+last,4*(n-1),5*(n-2)+6,3*n-4,0,n-1) if n>=2 and k else (k if n==1 else 0,0,0,0,0,0)
        assert (x,h,cx,ccx,p,m)==expected,(n,k,(x,h,cx,ccx,p,m),expected)
        checks+=1
    assert checks==254,checks
    print('PASS: 254 complete actual unconditional-adder vectors and 254 fixed-control variants, including zero patterns and widths 0–6')
if __name__=='__main__': main()
