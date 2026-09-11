#!/usr/bin/env python3
"""Independent sparse-state replay of actual Lean signed lookup/add/clear programs."""
from pathlib import Path
import subprocess,tempfile,json,math,cmath
ROOT=Path(__file__).resolve().parents[1]
LEAN=r'''
import ShorECDLP.Submission.«2607_13816».Window.SignedLookup
open ShorECDLP ShorECDLP.Paper2607_13816 Quantum
private def row : Gate → List Int
 | .X a => [0,a]
 | .CX a b => [1,a,b]
 | .CCX a b c => [2,a,b,c]
 | .H a => [3,a]
 | .P dir k a => [4,a,k,if dir==.forward then 1 else -1]
private def encode : AdaptiveCircuit → Lean.Json
 | .done => Lean.toJson ([0] : List Nat)
 | .unitary gates next => Lean.Json.arr #[Lean.toJson (1:Nat),Lean.toJson (gates.map row),encode next]
 | .xMeasureReset w a b => Lean.Json.arr #[Lean.toJson (2:Nat),Lean.toJson w,encode a,encode b]
def main : IO Unit := do
 for n in [0:2] do
  let bits := if n==0 then [] else [1]
  let paths := if n==0 then [] else [2]
  let table := fun label => (2*label+1)%3
  let program := signedLookupModularAddProgram table bits paths ([3,4] : List Wire) ([5,6] : List Wire) (constantBits 2 1) 3 0 11 7 8 9 10
  IO.println s!"{n}:{(encode program).compress}"
'''
def add(dst,key,val): dst[key]=dst.get(key,0j)+val

def gate(row,state):
    out={}; kind,*args=row
    for word,amp in state.items():
        if kind in (0,1,2):
            controls=args[:-1]; target=args[-1]
            result=word^(1<<target) if all(word>>w&1 for w in controls) else word
            add(out,result,amp)
        elif kind==3:
            w=args[0]; bit=word>>w&1
            add(out,word&~(1<<w),amp/math.sqrt(2))
            add(out,word|(1<<w),amp*(-1 if bit else 1)/math.sqrt(2))
        elif kind==4:
            w,k,d=args
            add(out,word,amp*(cmath.exp(d*2j*math.pi/(2**k)) if word>>w&1 else 1))
        else: raise AssertionError(row)
    return {k:v for k,v in out.items() if abs(v)>1e-12}

def run(node,state,history=()):
    if node[0]==0: return [(history,state)]
    if node[0]==1:
        for row in node[1]: state=gate(row,state)
        return run(node[2],state,history)
    _,w,a,b=node; branches=[]
    for outcome,tail in enumerate((a,b)):
        projected={}
        for word,amp in state.items():
            sign=-1 if outcome and word>>w&1 else 1
            add(projected,word&~(1<<w),amp*sign/math.sqrt(2))
        branches+=run(tail,projected,history+(outcome,))
    return branches
if __name__=='__main__':
    with tempfile.TemporaryDirectory(prefix='signed-lookup-') as directory:
        source=Path(directory)/'Check.lean';source.write_text(LEAN)
        out=subprocess.run(['lake','env','lean','--run',str(source)],cwd=ROOT,check=True,text=True,capture_output=True).stdout
    cases=branches=0
    for line in out.splitlines():
        raw,tree=line.split(':',1);n=int(raw);tree=json.loads(tree)
        basis=[1|(addr<<1)|(acc<<5)|(sign<<11)|(spectator<<12) for addr in range(2**n) for acc in range(3) for sign in range(2) for spectator in range(2)]
        states=[{basis[0]:1+0j},{basis[-1]:1+0j}]
        states += [{w:cmath.exp(1j*(i+1))/math.sqrt(len(basis)) for i,w in enumerate(basis)}]
        for state in states:
            expected={}
            for word,amp in state.items():
                address=(word>>1&1) if n else 0
                value=(2*address+1)%3
                result=((word>>5&3)+(value if word>>11&1 else -value))%3
                add(expected,(word&~(3<<5))|(result<<5),amp)
            outputs=run(tree,state)
            assert abs(sum(abs(a)**2 for _,v in outputs for a in v.values())-1)<1e-9
            for history,actual in outputs:
                coefficient=2**(-len(history)/2)
                for w in actual.keys()|expected.keys():
                    assert abs(actual.get(w,0)-coefficient*expected.get(w,0))<1e-9,(n,history,w)
                branches+=1
            cases+=1
    print(f'{cases} basis/superposition inputs, {branches} actual adaptive branches: modular result, phase and full frame passed')
