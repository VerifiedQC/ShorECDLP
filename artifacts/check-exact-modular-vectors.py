#!/usr/bin/env python3
"""Compare actual small modular/loop trees against independent exact integer formulas."""
from pathlib import Path
import subprocess
import tempfile
ROOT=Path(__file__).resolve().parents[1]
LEAN_CHECK=r'''
import ShorECDLP.Submission.«2607_13816».Arithmetic.ConstantPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».Arithmetic.LoopPrimitiveCounts
open ShorECDLP ShorECDLP.Paper2607_13816 Quantum
def emit (tag : String) (n p k m : Nat) (a : AdaptiveCircuit) : IO Unit := do
  let v := primitiveResources a
  IO.println s!"{tag} {n} {p} {k} {m} {v.x} {v.h} {v.cnot} {v.toffoli} {v.phase} {v.measurements}"
def main : IO Unit := do
  for n in [2:6] do
    let input := List.range' 6 n
    let acc := List.range' (6+n) n
    let bits := fun k => (List.range n).map (Nat.testBit k)
    for p in [3:2^n] do
      if p%2==1 then
        let correction := bits (2^n-p)
        emit "add" n p 0 0 (controlledModularAdd input acc correction p 0 1 2 3 4)
        emit "sub" n p 0 0 (controlledModularSub input acc (bits p) p 0 1 2 3 4)
        emit "double" n p 0 0 (modularDouble acc input correction p 1 2 3 4)
        emit "halve" n p 0 0 (modularHalve acc input (bits p) p 1 2 3 4)
        if n<4 then
          for k in [0:p] do
            emit "constant" n p k 0 (controlledConstantModularAdd acc input (bits k) correction p 0 1 2 3 4)
            emit "unconditional" n p k 0 (uncontrolledConstantModularAdd acc input (bits k) correction p 1 2 3 4)
          emit "negate" n p 0 0 (controlledModularNegate acc input (bits p) 0 1 2 3 4)
    if n<4 then
      let p := 2^n-1
      for m in [0:3] do
        let controls := List.range' (6+2*n) m
        emit "horner" n p 0 m (hornerMul controls input acc (bits 1) p 1 2 3 4)
        emit "inverse" n p 0 m (hornerMulInverse controls input acc (bits p) p 1 2 3 4)
        emit "square" n p 0 m (squareLoop controls input acc (bits 1) p 0 1 2 3 4)
        emit "unsquare" n p 0 m (squareLoopInverse controls input acc (bits p) p 0 1 2 3 4)
'''
ZERO=(0,)*6
def add(*vs): return tuple(map(sum,zip(*vs)))
def scale(n,v): return tuple(n*x for x in v)
def pop(n): return bin(n).count('1')
def adder(n,k,controlled):
    if k==0:return ZERO
    extra=8*(k&1)+10*pop((k>>1)&((1<<(n-2))-1))+((k>>(n-1))&1)
    return (4*n-2+(0 if controlled else extra),4*(n-1),5*(n-2)+6+(extra if controlled else 0),3*n-4,0,n-1)
def ge(n,p,controlled):
    flip=(0,0,1,0,0,0) if controlled else (1,0,0,0,0,0)
    if p==0:return flip
    if p>=1<<n:return ZERO
    bits=(1<<n)-p; extra=7*(bits&1)+9*pop(bits>>1)
    return (2*n+(0 if controlled else extra),4*n,6*n+1+(extra if controlled else 0),3*n-1,0,n)
def lt(n,p,controlled):
    if p==0:return ZERO
    return add((0,0,1,0,0,0) if controlled else (1,0,0,0,0,0),ge(n,p,controlled))
def expected(tag,n,p,k,m):
    correction=(1<<n)-p
    a=add((2*n+4,0,8*n,5*n+2,0,0),ge(n,p,False),adder(n,correction,True))
    sub=add((2*n+4,0,8*n,5*n+2,0,0),ge(n,p,False),adder(n,p,True))
    double=add((0,0,3*n,0,0,0),ge(n,p,False),adder(n,correction,True))
    halve=add((0,0,3*n,0,0,0),ge(n,p,False),adder(n,p,True))
    if tag in ('add','sub','double','halve'):return dict(add=a,sub=sub,double=double,halve=halve)[tag]
    if tag in ('constant','unconditional'):
        ctrl=tag=='constant'
        return add(adder(n,k,ctrl),scale(2,lt(n,k,ctrl)),ge(n,p,False),adder(n,correction,True))
    if tag=='negate':return add(scale(2,ge(n,1,True)),(0,0,n,0,0,0),adder(n,1,True),adder(n,p,True))
    inverse=tag in ('inverse','unsquare');square=tag in ('square','unsquare')
    step=sub if inverse else a
    if square:step=add(step,(0,0,2,0,0,0))
    return add(scale(m,step),scale(max(m-1,0),halve if inverse else double))
def main():
    with tempfile.TemporaryDirectory(prefix='exact-modular-') as tmp:
        p=Path(tmp)/'Main.lean';p.write_text(LEAN_CHECK)
        result=subprocess.run(['lake','env','lean','--run',str(p)],cwd=ROOT,text=True,capture_output=True,check=True)
    checked=0
    for line in result.stdout.splitlines():
        tag,*fields=line.split();n,p,k,m,*v=map(int,fields)
        want=expected(tag,n,p,k,m)
        assert tuple(v)==want,(tag,n,p,k,m,v,want)
        checked+=1
    assert checked==168,checked
    print(f'PASS: {checked} actual modular, constant, negation and forward/inverse Horner/square circuits match all six exact components')
if __name__=='__main__':main()
