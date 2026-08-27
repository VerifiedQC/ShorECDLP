import ShorECDLP.Submission.EllipticCurve.AffineFormula
import ShorECDLP.Submission.EllipticCurve.PointRegister
import ShorECDLP.Submission.Arithmetic.ModSub
import ShorECDLP.Submission.Arithmetic.Predicates
import ShorECDLP.Submission.Arithmetic.Secp256k1Instance

namespace ShorECDLP
namespace Secp256k1

open Classical
open Arithmetic
open scoped ArithmeticNotation

/-!
# Clean addition of a classical secp256k1 point

This file constructs the reversible operation

    |R⟩ |0⟩ |0_work⟩
      ↦
    |R⟩ |R + C⟩ |0_work⟩

where

* `R` is a quantum secp256k1 point;
* `C` is a classical constant point;
* the input point is preserved;
* every scratch wire is restored.

For a finite constant `C = (x₂,y₂)`, the circuit implements the same
decision tree as `affineAdd`:

    R = O          -> C
    R = -C         -> O
    R = C          -> double R
    otherwise      -> generic affine addition

The generic affine formula is

    λ  = (y₁ - y₂) / (x₁ - x₂)
    x₃ = λ² - x₁ - x₂
    y₃ = λ(x₁ - x₃) - y₁

and doubling is

    λ  = 3x₁² / 2y₁
    x₃ = λ² - 2x₁
    y₃ = λ(x₁ - x₃) - y₁.

All field operations are built from the concrete width-257 arithmetic
already supplied by `Secp256k1Instance`.
-/

private def fieldWidth : Nat :=
  Secp256k1Instance.fieldWidth

/-! -------------------------------------------------------------------------
    Wire relabelling

`Secp256k1Instance` gives us one concrete field-arithmetic circuit whose
wires start at zero.  Point addition needs to place that arithmetic engine
inside a larger circuit, so we translate every arithmetic wire by a fixed
offset.

This does not introduce a new gate.  It simply renames the wires of the
already-defined circuit.
------------------------------------------------------------------------- -/

def shiftGate (offset : Wire) : Gate → Gate
  | .X t       => .X (offset + t)
  | .H t       => .H (offset + t)
  | .CX c t    => .CX (offset + c) (offset + t)
  | .CCX a b t => .CCX (offset + a) (offset + b) (offset + t)
  | .P dir k t => .P dir k (offset + t)

def shiftCircuit (offset : Wire) (c : Circuit) : Circuit :=
  c.map (shiftGate offset)

def shiftWires (offset : Wire) (ws : List Wire) : List Wire :=
  ws.map fun w => offset + w

/-! -------------------------------------------------------------------------
    Local PointAdd workspace

The public registers `pointReg` and `outReg` are supplied to `pointAdd`.

Everything else is allocated consecutively beginning at `workStart`.

There are seven 257-bit field registers:

    xField, yField
        Copies of the quantum point coordinates, padded from 256 to 257 bits.

    t0 ... t4
        Five reusable field temporaries.  Their meanings change as the
        affine formulas progress.

After those come the predicate workspace, branch flags, one candidate
point, and the selected result.

The much larger multiplication/exponentiation scratch is placed after this
small local workspace and is reused by every field operation.
------------------------------------------------------------------------- -/

private def fieldAreaSize : Nat :=
  7 * fieldWidth

private def constOffset : Nat :=
  fieldAreaSize

private def zeroHistoryOffset : Nat :=
  constOffset + 256

private def xDifferenceOffset : Nat :=
  zeroHistoryOffset + 1

private def xHistoryOffset : Nat :=
  xDifferenceOffset + 256

private def yDifferenceOffset : Nat :=
  xHistoryOffset + 256

private def yHistoryOffset : Nat :=
  yDifferenceOffset + 256

private def flagOffset : Nat :=
  yHistoryOffset + 256

private def candidateOffset : Nat :=
  flagOffset + 6

private def selectedOffset : Nat :=
  candidateOffset + pointWidth

private def localWorkSize : Nat :=
  selectedOffset + pointWidth

/-! The seven reusable 257-bit registers. -/

def pointAddX (workStart : Wire) : List Wire :=
  List.range' workStart fieldWidth

def pointAddY (workStart : Wire) : List Wire :=
  List.range' (workStart + fieldWidth) fieldWidth

def pointAddT0 (workStart : Wire) : List Wire :=
  List.range' (workStart + 2 * fieldWidth) fieldWidth

def pointAddT1 (workStart : Wire) : List Wire :=
  List.range' (workStart + 3 * fieldWidth) fieldWidth

def pointAddT2 (workStart : Wire) : List Wire :=
  List.range' (workStart + 4 * fieldWidth) fieldWidth

def pointAddT3 (workStart : Wire) : List Wire :=
  List.range' (workStart + 5 * fieldWidth) fieldWidth

def pointAddT4 (workStart : Wire) : List Wire :=
  List.range' (workStart + 6 * fieldWidth) fieldWidth

/-!
Temporary 256-bit classical-coordinate register.

It is used only while computing

    x_R = x_C
    y_R = -y_C.

The constant is loaded, the clean equality predicate is computed, and the
constant is immediately unloaded.
-/

def pointAddConst (workStart : Wire) : List Wire :=
  List.range' (workStart + constOffset) 256

/-! Predicate histories used by `zeroFlag` and `equalFlag`. -/

def pointAddZeroHistory (workStart : Wire) : List Wire :=
  [workStart + zeroHistoryOffset]

def pointAddXDifference (workStart : Wire) : List Wire :=
  List.range' (workStart + xDifferenceOffset) 256

def pointAddXHistory (workStart : Wire) : List Wire :=
  List.range' (workStart + xHistoryOffset) 256

def pointAddYDifference (workStart : Wire) : List Wire :=
  List.range' (workStart + yDifferenceOffset) 256

def pointAddYHistory (workStart : Wire) : List Wire :=
  List.range' (workStart + yHistoryOffset) 256

/-!
Branch flags.

`infinityFlag`
    1 iff the quantum input point is O.

`xEqFlag`
    1 iff x_R = x_C.

`yNegFlag`
    1 iff y_R = -y_C.

`genericFlag`
    1 iff R is finite and x_R ≠ x_C.

`pairFlag`
    temporary conjunction x_R = x_C and y_R ≠ -y_C.

`doubleFlag`
    1 iff R is finite and the doubling branch must be used.
-/

def pointAddInfinityFlag (workStart : Wire) : Wire :=
  workStart + flagOffset

def pointAddXEqFlag (workStart : Wire) : Wire :=
  workStart + flagOffset + 1

def pointAddYNegFlag (workStart : Wire) : Wire :=
  workStart + flagOffset + 2

def pointAddGenericFlag (workStart : Wire) : Wire :=
  workStart + flagOffset + 3

def pointAddPairFlag (workStart : Wire) : Wire :=
  workStart + flagOffset + 4

def pointAddDoubleFlag (workStart : Wire) : Wire :=
  workStart + flagOffset + 5

/-!
`candidate` is reused:

* first it stores the generic-addition point;
* then the doubling point;
* finally the classical constant C.

After each use it is uncomputed back to zero.

`selected` accumulates exactly one of these mutually-exclusive branches.
-/

def pointAddCandidate (workStart : Wire) : List Wire :=
  List.range' (workStart + candidateOffset) pointWidth

def pointAddSelected (workStart : Wire) : List Wire :=
  List.range' (workStart + selectedOffset) pointWidth

/-!
The concrete M1 arithmetic engine is placed immediately after the local
PointAdd workspace.

Every field operation below loads its operands into this engine, runs the
already-defined concrete arithmetic circuit, copies the result out, and
reverses the engine.  Therefore this same workspace can be reused for every
field operation in one point addition.
-/

def pointAddArithmeticOffset (workStart : Wire) : Wire :=
  workStart + localWorkSize

def pointAddArithmeticWork (workStart : Wire) : List Wire :=
  shiftWires
    (pointAddArithmeticOffset workStart)
    Secp256k1Instance.secpLayout.allWires

def pointAddWork (workStart : Wire) : List Wire :=
  List.range' workStart localWorkSize ++
    pointAddArithmeticWork workStart

/-! -------------------------------------------------------------------------
    Small reversible helpers
------------------------------------------------------------------------- -/

/--
Conditionally XOR-copy one aligned register into another.

If `control = 0`, `dst` is unchanged.
If `control = 1`, `dst := dst XOR src`.

When `dst` starts at zero this is a controlled copy.
-/
def controlledCopyReg (control : Wire) :
    List Wire → List Wire → Circuit
  | s :: src, d :: dst =>
      circuit! {
        gate! Gate.CCX control s d;
        controlledCopyReg control src dst
      }
  | _, _ => circuit! {}

/--
Pack two 257-bit field values into the 513-bit finite-point representation.

Only the low 256 bits of each field register are used.  The most-significant
257th arithmetic bit is zero for every canonical field element.
-/
def packFinitePoint
    (x y point : List Wire) : Circuit :=
  circuit! {
    loadConst (PointRegister.tag point) 1;
    Arithmetic.copyReg
      (x.take 256)
      (PointRegister.x point);
    Arithmetic.copyReg
      (y.take 256)
      (PointRegister.y point)
  }

/-! -------------------------------------------------------------------------
    Reusable concrete field operations

These wrappers let PointAdd treat the fixed `Secp256k1Instance` circuits
as ordinary clean operations on arbitrary PointAdd registers.

Each wrapper has the conceptual behavior

    |a⟩ |b⟩ |0_out⟩ |0_engine⟩
      ->
    |a⟩ |b⟩ |f(a,b)⟩ |0_engine⟩.

The arithmetic engine is clean again before the wrapper returns.
------------------------------------------------------------------------- -/

private def engineAddLhs (offset : Wire) : List Wire :=
  shiftWires offset Secp256k1Instance.secpAddLayout.lhs

private def engineAddRhs (offset : Wire) : List Wire :=
  shiftWires offset Secp256k1Instance.secpAddLayout.rhs

private def engineAddOut (offset : Wire) : List Wire :=
  shiftWires offset Secp256k1Instance.secpAddLayout.out

def fieldAdd
    (offset : Wire)
    (lhs rhs out : List Wire) : Circuit :=
  let a := engineAddLhs offset
  let b := engineAddRhs offset
  let r := engineAddOut offset
  let core :=
    shiftCircuit offset Secp256k1Instance.secpAddProgram
  circuit! {
    Arithmetic.copyReg lhs a;
    Arithmetic.copyReg rhs b;

    core;

    Arithmetic.copyReg r out;

    core.reverse;

    Arithmetic.copyReg rhs b;
    Arithmetic.copyReg lhs a
  }

/-!
A concrete modular-subtraction core using the same first arithmetic blocks
as the concrete modular adder.

Relative blocks:

    0  lhs
    1  rhs
    2  out
    3  raw subtraction
    4  modulus constant
    5  corrected candidate
    6  subtraction carry-in
    7  subtraction carry bank
    8  correction carry-in
    9  correction carry bank
-/

private def fieldSubCore : Circuit :=
  modSub
    (Secp256k1Instance.reg 0).wires
    (Secp256k1Instance.reg 1).wires
    (Secp256k1Instance.reg 2).wires
    (Secp256k1Instance.reg 3).wires
    (Secp256k1Instance.reg 4).wires
    (Secp256k1Instance.reg 5).wires
    (Secp256k1Instance.bitWire 6)
    (Secp256k1Instance.reg 7).wires
    (Secp256k1Instance.bitWire 8)
    (Secp256k1Instance.reg 9).wires
    p

private def engineSubLhs (offset : Wire) : List Wire :=
  shiftWires offset (Secp256k1Instance.reg 0).wires

private def engineSubRhs (offset : Wire) : List Wire :=
  shiftWires offset (Secp256k1Instance.reg 1).wires

private def engineSubOut (offset : Wire) : List Wire :=
  shiftWires offset (Secp256k1Instance.reg 2).wires

def fieldSub
    (offset : Wire)
    (lhs rhs out : List Wire) : Circuit :=
  let a := engineSubLhs offset
  let b := engineSubRhs offset
  let r := engineSubOut offset
  let core := shiftCircuit offset fieldSubCore
  circuit! {
    Arithmetic.copyReg lhs a;
    Arithmetic.copyReg rhs b;

    core;

    Arithmetic.copyReg r out;

    core.reverse;

    Arithmetic.copyReg rhs b;
    Arithmetic.copyReg lhs a
  }

/--
Specialized subtraction by a classical constant.

This avoids reserving a permanent 257-bit register for every classical
constant appearing in the affine formulas.
-/
def fieldSubConst
    (offset : Wire)
    (lhs : List Wire)
    (c : Nat)
    (out : List Wire) : Circuit :=
  let a := engineSubLhs offset
  let b := engineSubRhs offset
  let r := engineSubOut offset
  let core := shiftCircuit offset fieldSubCore
  circuit! {
    Arithmetic.copyReg lhs a;
    loadConst b c;

    core;

    Arithmetic.copyReg r out;

    core.reverse;

    loadConst b c;
    Arithmetic.copyReg lhs a
  }

private def engineMulLhs (offset : Wire) : List Wire :=
  shiftWires offset Secp256k1Instance.secpMulLayout.lhs

private def engineMulRhs (offset : Wire) : List Wire :=
  shiftWires offset Secp256k1Instance.secpMulLayout.rhs

private def engineMulOut (offset : Wire) : List Wire :=
  shiftWires offset Secp256k1Instance.secpMulLayout.out

def fieldMul
    (offset : Wire)
    (lhs rhs out : List Wire) : Circuit :=
  let a := engineMulLhs offset
  let b := engineMulRhs offset
  let r := engineMulOut offset
  let core :=
    shiftCircuit offset Secp256k1Instance.secpMulProgram
  circuit! {
    Arithmetic.copyReg lhs a;
    Arithmetic.copyReg rhs b;

    core;

    Arithmetic.copyReg r out;

    core.reverse;

    Arithmetic.copyReg rhs b;
    Arithmetic.copyReg lhs a
  }

/-!
Fermat inversion.

The concrete exponentiation circuit computes

    a^(p-2) = a⁻¹

for nonzero field elements.

The exponent register is loaded with the classical constant `p - 2`.
-/

private def engineInvBase (offset : Wire) : List Wire :=
  shiftWires offset Secp256k1Instance.secpLayout.lhs

private def engineInvExponent (offset : Wire) : List Wire :=
  shiftWires offset Secp256k1Instance.secpLayout.rhs

private def engineInvOut (offset : Wire) : List Wire :=
  shiftWires offset Secp256k1Instance.secpLayout.out

def fieldInv
    (offset : Wire)
    (input out : List Wire) : Circuit :=
  let base := engineInvBase offset
  let exponent := engineInvExponent offset
  let result := engineInvOut offset
  let core :=
    shiftCircuit offset Secp256k1Instance.secpProgram
  circuit! {
    Arithmetic.copyReg input base;
    loadConst exponent (p - 2);

    core;

    Arithmetic.copyReg result out;

    core.reverse;

    loadConst exponent (p - 2);
    Arithmetic.copyReg input base
  }

/-! -------------------------------------------------------------------------
    Generic affine addition
------------------------------------------------------------------------- -/

/--
Compute the generic affine coordinates for

    R = (x₁,y₁)
    C = (x₂,y₂)

with `x₁ ≠ x₂`.

Only five temporary field registers are used.

At the end:

    t2 = x₃
    t4 = y₃

while the other temporaries contain reversible history that is removed when
this circuit is run backwards.
-/
def genericPointCompute
    (workStart : Wire)
    (xC yC : Fp) : Circuit :=
  let offset := pointAddArithmeticOffset workStart

  let x := pointAddX workStart
  let y := pointAddY workStart

  let t0 := pointAddT0 workStart
  let t1 := pointAddT1 workStart
  let t2 := pointAddT2 workStart
  let t3 := pointAddT3 workStart
  let t4 := pointAddT4 workStart

  /- t0 = y₁ - y₂ -/
  let numerator :=
    fieldSubConst offset y yC.val t0

  /- t1 = x₁ - x₂ -/
  let denominator :=
    fieldSubConst offset x xC.val t1

  /- t2 = (x₁ - x₂)⁻¹ -/
  let inverse :=
    fieldInv offset t1 t2

  /- t3 = λ -/
  let slope :=
    fieldMul offset t0 t2 t3

  /- After λ has been obtained, numerator/denominator/inverse are no
     longer needed.  Uncomputing them frees t0,t1,t2 for reuse. -/

  /- t0 = λ² -/
  let slopeSq :=
    fieldMul offset t3 t3 t0

  /- t1 = λ² - x₁ -/
  let minusX :=
    fieldSub offset t0 x t1

  /- t2 = x₃ = λ² - x₁ - x₂ -/
  let xOut :=
    fieldSubConst offset t1 xC.val t2

  /- Once x₃ is available, λ² and λ²-x₁ can be uncomputed. -/

  /- t0 = x₁ - x₃ -/
  let xDifference :=
    fieldSub offset x t2 t0

  /- t1 = λ(x₁-x₃) -/
  let yProduct :=
    fieldMul offset t3 t0 t1

  /- t4 = y₃ -/
  let yOut :=
    fieldSub offset t1 y t4

  circuit! {
    numerator;
    denominator;
    inverse;
    slope;

    inverse.reverse;
    denominator.reverse;
    numerator.reverse;

    slopeSq;
    minusX;
    xOut;

    minusX.reverse;
    slopeSq.reverse;

    xDifference;
    yProduct;
    yOut
  }

/-! -------------------------------------------------------------------------
    Point doubling
------------------------------------------------------------------------- -/

/--
Cleanly compute `3*x²` into `out`.

`scratch0` and `scratch1` are restored before the operation returns.
-/
def threeXSquared
    (offset : Wire)
    (x scratch0 scratch1 out : List Wire) : Circuit :=
  let square :=
    fieldMul offset x x scratch0
  let twice :=
    fieldAdd offset scratch0 scratch0 scratch1
  let three :=
    fieldAdd offset scratch1 scratch0 out
  circuit! {
    square;
    twice;
    three;
    twice.reverse;
    square.reverse
  }

/--
Compute the affine doubling coordinates.

For secp256k1, the curve coefficient `a` is zero, hence

    λ = 3x² / 2y.

At the end:

    t2 = x₃
    t4 = y₃.
-/
def doublePointCompute
    (workStart : Wire) : Circuit :=
  let offset := pointAddArithmeticOffset workStart

  let x := pointAddX workStart
  let y := pointAddY workStart

  let t0 := pointAddT0 workStart
  let t1 := pointAddT1 workStart
  let t2 := pointAddT2 workStart
  let t3 := pointAddT3 workStart
  let t4 := pointAddT4 workStart

  /- t2 = 3x₁²; t0,t1 are returned to zero. -/
  let numerator :=
    threeXSquared offset x t0 t1 t2

  /- t0 = 2y₁ -/
  let denominator :=
    fieldAdd offset y y t0

  /- t1 = (2y₁)⁻¹ -/
  let inverse :=
    fieldInv offset t0 t1

  /- t3 = λ -/
  let slope :=
    fieldMul offset t2 t1 t3

  /- t0 = λ² -/
  let slopeSq :=
    fieldMul offset t3 t3 t0

  /- t1 = 2x₁ -/
  let twoX :=
    fieldAdd offset x x t1

  /- t2 = x₃ = λ² - 2x₁ -/
  let xOut :=
    fieldSub offset t0 t1 t2

  /- t0 = x₁ - x₃ -/
  let xDifference :=
    fieldSub offset x t2 t0

  /- t1 = λ(x₁-x₃) -/
  let yProduct :=
    fieldMul offset t3 t0 t1

  /- t4 = y₃ -/
  let yOut :=
    fieldSub offset t1 y t4

  circuit! {
    numerator;
    denominator;
    inverse;
    slope;

    inverse.reverse;
    denominator.reverse;
    numerator.reverse;

    slopeSq;
    twoX;
    xOut;

    twoX.reverse;
    slopeSq.reverse;

    xDifference;
    yProduct;
    yOut
  }

/-! -------------------------------------------------------------------------
    Exceptional-case flags
------------------------------------------------------------------------- -/

/--
Compute the branch flags for addition by the finite constant `(xC,yC)`.

For a valid input point exactly one of the following happens:

* `infinityFlag = 1`
      R = O

* `genericFlag = 1`
      R is finite and x_R ≠ x_C

* `doubleFlag = 1`
      R is finite, x_R = x_C, and y_R ≠ -y_C

* all three are zero
      R = -C, so the result is O.

The inverse-pair branch deliberately requires no output candidate:
the canonical encoding of O is all zero, and `selected` already starts zero.
-/
def pointAddFlags
    (pointReg : List Wire)
    (workStart : Wire)
    (xC yC : Fp) : Circuit :=
  let constReg := pointAddConst workStart

  let infinityFlag := pointAddInfinityFlag workStart
  let xEqFlag := pointAddXEqFlag workStart
  let yNegFlag := pointAddYNegFlag workStart
  let genericFlag := pointAddGenericFlag workStart
  let pairFlag := pointAddPairFlag workStart
  let doubleFlag := pointAddDoubleFlag workStart

  circuit! {
    /- infinityFlag = (R = O) -/
    zeroFlag
      (PointRegister.tag pointReg)
      infinityFlag
      (pointAddZeroHistory workStart);

    /- xEqFlag = (x_R = x_C) -/
    loadConst constReg xC.val;
    equalFlag
      (PointRegister.x pointReg)
      constReg
      xEqFlag
      (pointAddXDifference workStart)
      (pointAddXHistory workStart);
    loadConst constReg xC.val;

    /- yNegFlag = (y_R = -y_C) -/
    loadConst constReg (-yC).val;
    equalFlag
      (PointRegister.y pointReg)
      constReg
      yNegFlag
      (pointAddYDifference workStart)
      (pointAddYHistory workStart);
    loadConst constReg (-yC).val;

    /- genericFlag = !infinityFlag && !xEqFlag -/
    gate! Gate.X infinityFlag;
    gate! Gate.X xEqFlag;
    gate! Gate.CCX infinityFlag xEqFlag genericFlag;
    gate! Gate.X xEqFlag;
    gate! Gate.X infinityFlag;

    /- pairFlag = xEqFlag && !yNegFlag -/
    gate! Gate.X yNegFlag;
    gate! Gate.CCX xEqFlag yNegFlag pairFlag;
    gate! Gate.X yNegFlag;

    /- doubleFlag = !infinityFlag && pairFlag -/
    gate! Gate.X infinityFlag;
    gate! Gate.CCX infinityFlag pairFlag doubleFlag;
    gate! Gate.X infinityFlag
  }

/-! -------------------------------------------------------------------------
    Candidate branches
------------------------------------------------------------------------- -/

/--
Compute the generic point candidate, conditionally XOR it into `selected`,
then clean the candidate and every field temporary.
-/
def genericPointBranch
    (workStart : Wire)
    (xC yC : Fp) : Circuit :=
  let compute :=
    genericPointCompute workStart xC yC

  let pack :=
    packFinitePoint
      (pointAddT2 workStart)
      (pointAddT4 workStart)
      (pointAddCandidate workStart)

  circuit! {
    compute;
    pack;

    controlledCopyReg
      (pointAddGenericFlag workStart)
      (pointAddCandidate workStart)
      (pointAddSelected workStart);

    pack.reverse;
    compute.reverse
  }

/--
Compute the doubling candidate, conditionally XOR it into `selected`,
then clean the candidate and every field temporary.
-/
def doublePointBranch
    (workStart : Wire) : Circuit :=
  let compute :=
    doublePointCompute workStart

  let pack :=
    packFinitePoint
      (pointAddT2 workStart)
      (pointAddT4 workStart)
      (pointAddCandidate workStart)

  circuit! {
    compute;
    pack;

    controlledCopyReg
      (pointAddDoubleFlag workStart)
      (pointAddCandidate workStart)
      (pointAddSelected workStart);

    pack.reverse;
    compute.reverse
  }

/--
If the input point is infinity, the answer is the classical constant `C`.

The candidate register is loaded with `C`, conditionally copied, and
immediately cleared.
-/
def infinityPointBranch
    (workStart : Wire)
    (C : Point) : Circuit :=
  let candidate := pointAddCandidate workStart
  let load := loadConst candidate (encode C).val
  circuit! {
    load;

    controlledCopyReg
      (pointAddInfinityFlag workStart)
      candidate
      (pointAddSelected workStart);

    load
  }

/-! -------------------------------------------------------------------------
    Complete finite-constant computation
------------------------------------------------------------------------- -/

/-! -------------------------------------------------------------------------
    PointAdd finite computation: proof-oriented decomposition
------------------------------------------------------------------------- -/

-- The setup stage:

-- 1. copy the public x-coordinate into the padded arithmetic x-register;
-- 2. copy the public y-coordinate into the padded arithmetic y-register;
-- 3. compute the branch flags.

-- It does not touch `selected`.

def pointAddCopyX
    (pointReg : List Wire)
    (workStart : Wire) : Circuit :=
  Arithmetic.copyReg
    (PointRegister.x pointReg)
    ((pointAddX workStart).take 256)

def pointAddCopyY
    (pointReg : List Wire)
    (workStart : Wire) : Circuit :=
  Arithmetic.copyReg
    (PointRegister.y pointReg)
    ((pointAddY workStart).take 256)

def pointAddCoordinateCopies
    (pointReg : List Wire)
    (workStart : Wire) : Circuit :=
  pointAddCopyX pointReg workStart ++
    pointAddCopyY pointReg workStart

def pointAddSetup
    (pointReg : List Wire)
    (workStart : Wire)
    (xC yC : Fp) :
    Circuit :=
  pointAddCoordinateCopies pointReg workStart ++
    pointAddFlags pointReg workStart xC yC
/--
The branch stage.

The flags computed by `pointAddSetup` determine which, if any,
candidate is XORed into `selected`.

* genericFlag = 1  -> generic affine addition
* doubleFlag  = 1  -> doubling
* infinityFlag = 1 -> C
* all zero          -> O
-/
def pointAddBranches
    (workStart : Wire)
    {xC yC : Fp}
    (hC : curve.toAffine.Nonsingular xC yC) :
    Circuit :=
  circuit! {
    genericPointBranch workStart xC yC;
    doublePointBranch workStart;
    infinityPointBranch workStart (.some hC)
  }

/--
The portion of PointAdd scratch used by the three candidate branches.

`pointAddX` and `pointAddY` are deliberately not included: they contain
the copied input coordinates rather than zero.
-/
def pointAddBranchWork (workStart : Wire) : List Wire :=
  pointAddT0 workStart ++
  pointAddT1 workStart ++
  pointAddT2 workStart ++
  pointAddT3 workStart ++
  pointAddT4 workStart ++
  pointAddCandidate workStart ++
  pointAddSelected workStart ++
  pointAddArithmeticWork workStart

/--
The finite computation is exactly setup followed by the candidate branches.
-/
def pointAddFiniteCompute
    (pointReg : List Wire)
    (workStart : Wire)
    {xC yC : Fp}
    (hC : curve.toAffine.Nonsingular xC yC) :
    Circuit :=
  pointAddSetup pointReg workStart xC yC ++
    pointAddBranches workStart hC

/-! -------------------------------------------------------------------------
    Public PointAdd operation
------------------------------------------------------------------------- -/

/--
Clean out-of-place addition by a classical point.

For `C = O`, addition is just a register copy.

For finite `C`, first compute `R + C` into the private `selected` register,
copy it to `outReg`, and reverse the complete computation.

Thus the intended action is

    |R⟩ |0_out⟩ |0_work⟩
      ↦
    |R⟩ |R+C⟩ |0_work⟩.
-/
def pointAdd
    (pointReg outReg : List Wire)
    (workStart : Wire)
    (C : Point) :
    Circuit :=
  match C with
  | .zero =>
      Arithmetic.copyReg pointReg outReg

  | @WeierstrassCurve.Affine.Point.some _ _ _ _xC _yC hC =>
      let compute :=
        pointAddFiniteCompute pointReg workStart hC
      circuit! {
        compute;

        Arithmetic.copyReg
          (pointAddSelected workStart)
          outReg;

        compute.reverse
      }

/-! -------------------------------------------------------------------------
    Correctness proof decomposition

There are three genuinely different proof obligations.

1. `pointAddFiniteCompute_correct`
   Prove the actual elliptic-curve arithmetic: after the forward computation,
   `selected` contains `affineAdd R C`.

2. `pointAddFiniteCompute_structural`
   Prove that the forward circuit is a valid classical reversible computation,
   is confined to the PointAdd input/workspace, and that `selected` is part of
   that workspace.

3. `bennett_copyReg_eq_writeReg`
   A generic reversible-computing lemma: if `compute` produces a value in a
   scratch register, copying that value to a clean output and reversing
   `compute` leaves exactly that output written into the original state.

The final theorem then contains essentially no elliptic-curve arithmetic.
------------------------------------------------------------------------- -/

/--
Exact register copying.

If `src` contains `value` and `dst` is a clean, disjoint register of the
same width, then CNOT-copying `src` to `dst` has exactly the same whole-state
effect as `writeReg dst value`.

This is useful both for the `C = O` case and inside the Bennett argument.
-/
theorem copyReg_eq_writeReg_of_value
    (src dst work : List Wire)
    (st : BasisState)
    (value : Nat)
    (hlen : dst.length = src.length)
    (hnodup : (src ++ dst ++ work).Nodup)
    (hclean : Clean dst st)
    (hvalue : regValue src st = value)
    (_hbound : value < 2 ^ dst.length) :
    Classical.run (Arithmetic.copyReg src dst) st =
      writeReg dst value st := by
  have aux :
      ∀ (src dst : List Wire) (st : BasisState),
        dst.length = src.length →
        (src ++ dst).Nodup →
        Clean dst st →
        Classical.run (Arithmetic.copyReg src dst) st =
          writeReg dst (regValue src st) st := by
    intro src
    induction src with
    | nil =>
        intro dst st hlen hnd hclean
        have hdst : dst = [] := by
          apply List.length_eq_zero_iff.mp
          simpa using hlen
        subst dst
        rfl
    | cons s src ih =>
        intro dst st hlen hnd hclean
        cases dst with
        | nil =>
            simp at hlen
        | cons d dst =>
            have hlenTail : dst.length = src.length := by
              simpa using hlen

            obtain ⟨hsrcNd, hdstNd, hcross⟩ :=
              List.nodup_append.mp hnd
            obtain ⟨_, hsrcTailNd⟩ :=
              List.nodup_cons.mp hsrcNd
            obtain ⟨hdDst, hdstTailNd⟩ :=
              List.nodup_cons.mp hdstNd

            have htailNd : (src ++ dst).Nodup :=
              List.nodup_append.mpr
                ⟨hsrcTailNd, hdstTailNd,
                  fun a ha b hb =>
                    hcross a
                      (List.mem_cons_of_mem s ha)
                      b
                      (List.mem_cons_of_mem d hb)⟩

            have hdSrc : d ∉ src := by
              intro hd
              exact
                (hcross d
                  (List.mem_cons_of_mem s hd)
                  d
                  (List.mem_cons_self)) rfl

            let st₁ := Classical.applyGate (Gate.CX s d) st

            have hcleanTail : Clean dst st₁ := by
              intro w hw
              change
                st[d ↦ Bool.xor (st d) (st s)] w = false
              have hwd : w ≠ d := by
                intro h
                subst w
                exact hdDst hw
              rw [upd_other _ _ _ hwd]
              exact hclean w (List.mem_cons_of_mem d hw)

            have hsrcKeep :
                regValue src st₁ = regValue src st := by
              change
                regValue src
                    (st[d ↦ Bool.xor (st d) (st s)]) =
                  regValue src st
              exact
                regValue_upd_not_mem src st d
                  (Bool.xor (st d) (st s)) hdSrc

            have hbit :
                (regValue (s :: src) st).testBit 0 = st s := by
              rw [regValue_cons, Nat.testBit_zero]
              cases hs : st s <;>
                simp [ Nat.add_mod]

            have hdiv :
                regValue (s :: src) st / 2 =
                  regValue src st := by
              rw [regValue_cons]
              cases hs : st s <;> simp ; omega

            have hst₁ :
                st₁ =
                  st[d ↦
                    (regValue (s :: src) st).testBit 0] := by
              simp only [st₁, Classical.applyGate]
              rw [hclean d (List.mem_cons_self)]
              simp [hbit]

            have hih :=
              ih dst st₁ hlenTail htailNd hcleanTail

            rw [Arithmetic.copyReg, Classical.run_cons]
            change
              Classical.run (Arithmetic.copyReg src dst) st₁ =
                writeReg (d :: dst)
                  (regValue (s :: src) st) st
            rw [hih, hsrcKeep, writeReg, hdiv, ← hst₁]

  have hnd : (src ++ dst).Nodup :=
    (List.nodup_append.mp hnodup).1

  calc
    Classical.run (Arithmetic.copyReg src dst) st =
        writeReg dst (regValue src st) st :=
      aux src dst st hlen hnd hclean
    _ = writeReg dst value st := by rw [hvalue]


def pointAddFlagWork (workStart : Wire) : List Wire :=
  pointAddConst workStart ++
  pointAddZeroHistory workStart ++
  pointAddXDifference workStart ++
  pointAddXHistory workStart ++
  pointAddYDifference workStart ++
  pointAddYHistory workStart ++
  [
    pointAddInfinityFlag workStart,
    pointAddXEqFlag workStart,
    pointAddYNegFlag workStart,
    pointAddGenericFlag workStart,
    pointAddPairFlag workStart,
    pointAddDoubleFlag workStart
  ]

theorem pointAddCopyX_correct
    (pointReg outReg : List Wire)
    (workStart : Wire)
    (st : BasisState)
    (hpointLength : pointReg.length = pointWidth)
    (hnodup :
      (pointReg ++ outReg ++ pointAddWork workStart).Nodup)
    (hclean :
      Clean (pointAddWork workStart) st) :
    let after :=
      Classical.run (pointAddCopyX pointReg workStart) st
    AgreesOn pointReg st after ∧
      regValue (pointAddX workStart) after =
        regValue (PointRegister.x pointReg) st ∧
      Clean
        (pointAddY workStart ++
         pointAddFlagWork workStart ++
         pointAddBranchWork workStart)
        after := by
  dsimp

  have hlocalSizeEq : localWorkSize = 4112 := by
    norm_num [localWorkSize, selectedOffset, candidateOffset, flagOffset,
      yHistoryOffset, yDifferenceOffset, xHistoryOffset,
      xDifferenceOffset, zeroHistoryOffset, constOffset, fieldAreaSize,
      fieldWidth, Secp256k1Instance.fieldWidth, pointWidth]

  have hlocalSize : 257 ≤ localWorkSize := by omega

  have hdstEq :
      (pointAddX workStart).take 256 =
        List.range' workStart 256 := by
    simp [pointAddX, fieldWidth, Secp256k1Instance.fieldWidth,
      List.take_range'_of_length_ge]

  have hdstWork :
      ∀ w ∈ (pointAddX workStart).take 256,
        w ∈ pointAddWork workStart := by
    intro w hw
    rw [hdstEq] at hw
    have hbounds := List.mem_range'_1.mp hw
    rw [pointAddWork]
    apply List.mem_append_left
    exact List.mem_range'_1.mpr ⟨hbounds.1, by omega⟩

  have hsrcMem :
      ∀ w ∈ PointRegister.x pointReg, w ∈ pointReg := by
    intro w hw
    change w ∈ (pointReg.drop 1).take 256 at hw
    exact List.mem_of_mem_drop (List.mem_of_mem_take hw)

  obtain ⟨hpublicNodup, _hworkNodup, hpublicWork⟩ :=
    List.nodup_append.mp hnodup
  obtain ⟨hpointNodup, _houtNodup, _hpointOut⟩ :=
    List.nodup_append.mp hpublicNodup

  have hsrcNodup : (PointRegister.x pointReg).Nodup := by
    apply List.Nodup.sublist
      ((List.take_sublist 256 (pointReg.drop 1)).trans
        (List.drop_sublist 1 pointReg))
    exact hpointNodup

  have hdstNodup : ((pointAddX workStart).take 256).Nodup := by
    rw [hdstEq]
    exact List.nodup_range'

  have hcopyNodup :
      (PointRegister.x pointReg ++
        (pointAddX workStart).take 256).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hsrcNodup, hdstNodup, ?_⟩
    intro a ha b hb
    exact hpublicWork a
      (List.mem_append_left outReg (hsrcMem a ha))
      b (hdstWork b hb)

  have hdstClean :
      Clean ((pointAddX workStart).take 256) st :=
    Arithmetic.Clean.mono hclean hdstWork

  have hcopyValue :
      regValue ((pointAddX workStart).take 256)
          (Classical.run (pointAddCopyX pointReg workStart) st) =
        regValue (PointRegister.x pointReg) st := by
    simpa only [pointAddCopyX] using
      (Arithmetic.copyReg_correct
        (PointRegister.x pointReg)
        ((pointAddX workStart).take 256)
        st
        (by
          rw [hdstEq]
          simpa using
            (PointRegister.x_length pointReg hpointLength).symm)
        hcopyNodup hdstClean)

  have hother (w : Wire)
      (hw : w ∉ (pointAddX workStart).take 256) :
      Classical.run (pointAddCopyX pointReg workStart) st w = st w := by
    simpa only [pointAddCopyX] using
      (Arithmetic.copyReg_other w
        (PointRegister.x pointReg)
        ((pointAddX workStart).take 256) st hw)

  have hpointAgree :
      AgreesOn pointReg st
        (Classical.run (pointAddCopyX pointReg workStart) st) := by
    intro w hw
    apply hother
    intro hdst
    exact
      (hpublicWork w (List.mem_append_left outReg hw)
        w (hdstWork w hdst)) rfl

  have hhighNotDst :
      workStart + 256 ∉ (pointAddX workStart).take 256 := by
    rw [hdstEq]
    simp [List.mem_range'_1]

  have hhighWork : workStart + 256 ∈ pointAddWork workStart := by
    rw [pointAddWork]
    apply List.mem_append_left
    exact List.mem_range'_1.mpr ⟨by omega, by omega⟩

  have hhighClean :
      Clean [workStart + 256]
        (Classical.run (pointAddCopyX pointReg workStart) st) := by
    intro w hw
    simp only [List.mem_singleton] at hw
    subst w
    rw [hother (workStart + 256) hhighNotDst]
    exact hclean (workStart + 256) hhighWork

  have hpointAddXShape :
      pointAddX workStart =
        PointRegister.padCoordinate
          ((pointAddX workStart).take 256)
          (workStart + 256) := by
    rw [PointRegister.padCoordinate, hdstEq]
    change
      List.range' workStart 257 =
        List.range' workStart 256 ++ [workStart + 256]
    simpa using
      (List.range'_concat (s := workStart) (n := 256) (step := 1))

  have hxValue :
      regValue (pointAddX workStart)
          (Classical.run (pointAddCopyX pointReg workStart) st) =
        regValue (PointRegister.x pointReg) st := by
    rw [hpointAddXShape]
    exact
      (PointRegister.regValue_padCoordinate_of_clean
        ((pointAddX workStart).take 256)
        (workStart + 256)
        (Classical.run (pointAddCopyX pointReg workStart) st)
        hhighClean).trans hcopyValue

  have rangeBounds
      (offset len : Nat)
      {w : Wire}
      (hw : workStart + offset ≤ w ∧
        w < workStart + offset + len)
      (hmin : 257 ≤ offset)
      (hmax : offset + len ≤ 4112) :
      workStart + 257 ≤ w ∧ w < workStart + 4112 := by
    constructor
    · exact (Nat.add_le_add_left hmin workStart).trans hw.1
    · apply hw.2.trans_le
      simpa [Nat.add_assoc] using
        (Nat.add_le_add_left hmax workStart)

  have wireBounds
      (offset : Nat)
      {w : Wire}
      (hw : w = workStart + offset)
      (hmin : 257 ≤ offset)
      (hmax : offset < 4112) :
      workStart + 257 ≤ w ∧ w < workStart + 4112 := by
    subst w
    exact
      ⟨Nat.add_le_add_left hmin workStart,
        Nat.add_lt_add_left hmax workStart⟩

  have hremainingFacts :
      ∀ w ∈
          (pointAddY workStart ++
            pointAddFlagWork workStart ++
            pointAddBranchWork workStart),
        workStart + 257 ≤ w ∧ w ∈ pointAddWork workStart := by
    intro w hw
    rcases List.mem_append.mp hw with hyFlag | hbranch
    · rcases List.mem_append.mp hyFlag with hy | hflag
      · have hyRaw :
            workStart + 257 ≤ w ∧ w < workStart + 257 + 257 := by
          simpa [pointAddY, fieldWidth,
            Secp256k1Instance.fieldWidth] using
            (List.mem_range'_1.mp hy)
        have hbounds :=
          rangeBounds 257 257 hyRaw (by omega) (by omega)
        have hge : workStart + 257 ≤ w := hbounds.1
        have hupper : w < workStart + localWorkSize := by
          rw [hlocalSizeEq]
          exact hbounds.2
        refine ⟨hge, ?_⟩
        rw [pointAddWork]
        apply List.mem_append_left
        apply List.mem_range'_1.mpr
        exact
          ⟨(Nat.le_add_right workStart 257).trans hge,
            hupper⟩
      · have hbounds :
            workStart + 257 ≤ w ∧ w < workStart + 4112 := by
          simp only [pointAddFlagWork, pointAddConst,
            pointAddZeroHistory, pointAddXDifference,
            pointAddXHistory, pointAddYDifference,
            pointAddYHistory, pointAddInfinityFlag,
            pointAddXEqFlag, pointAddYNegFlag,
            pointAddGenericFlag, pointAddPairFlag,
            pointAddDoubleFlag, List.mem_append,
            List.mem_cons,
            List.mem_range'_1] at hflag
          norm_num [localWorkSize, selectedOffset, candidateOffset,
            flagOffset, yHistoryOffset, yDifferenceOffset,
            xHistoryOffset, xDifferenceOffset, zeroHistoryOffset,
            constOffset, fieldAreaSize, fieldWidth,
            Secp256k1Instance.fieldWidth, pointWidth] at hflag
          rcases hflag with
              (((((h0 | h1) | h2) | h3) | h4) | h5) |
                (h6 | h7 | h8 | h9 | h10 | h11)
          · exact rangeBounds 1799 256 h0 (by omega) (by omega)
          · exact wireBounds 2055 h1 (by omega) (by omega)
          · exact rangeBounds 2056 256 h2 (by omega) (by omega)
          · exact rangeBounds 2312 256 h3 (by omega) (by omega)
          · exact rangeBounds 2568 256 h4 (by omega) (by omega)
          · exact rangeBounds 2824 256 h5 (by omega) (by omega)
          · exact wireBounds 3080 h6 (by omega) (by omega)
          · exact wireBounds 3081 h7 (by omega) (by omega)
          · exact wireBounds 3082 h8 (by omega) (by omega)
          · exact wireBounds 3083 h9 (by omega) (by omega)
          · exact wireBounds 3084 h10 (by omega) (by omega)
          · exact wireBounds 3085 h11 (by omega) (by omega)
        have hge : workStart + 257 ≤ w := hbounds.1
        have hupper : w < workStart + localWorkSize := by
          rw [hlocalSizeEq]
          exact hbounds.2
        refine ⟨hge, ?_⟩
        rw [pointAddWork]
        apply List.mem_append_left
        apply List.mem_range'_1.mpr
        exact
          ⟨(Nat.le_add_right workStart 257).trans hge,
            hupper⟩
    · rcases List.mem_append.mp hbranch with hlocal | harithmetic
      · have hbounds :
            workStart + 257 ≤ w ∧ w < workStart + 4112 := by
          simp only [pointAddT0, pointAddT1,
            pointAddT2, pointAddT3, pointAddT4,
            pointAddCandidate, pointAddSelected,
            List.mem_append, List.mem_range'_1] at hlocal
          norm_num [localWorkSize, selectedOffset, candidateOffset,
            flagOffset, yHistoryOffset, yDifferenceOffset,
            xHistoryOffset, xDifferenceOffset, zeroHistoryOffset,
            constOffset, fieldAreaSize, fieldWidth,
            Secp256k1Instance.fieldWidth, pointWidth] at hlocal
          rcases hlocal with
              (((((h0 | h1) | h2) | h3) | h4) | h5) | h6
          · exact rangeBounds 514 257 h0 (by omega) (by omega)
          · exact rangeBounds 771 257 h1 (by omega) (by omega)
          · exact rangeBounds 1028 257 h2 (by omega) (by omega)
          · exact rangeBounds 1285 257 h3 (by omega) (by omega)
          · exact rangeBounds 1542 257 h4 (by omega) (by omega)
          · exact rangeBounds 3086 513 h5 (by omega) (by omega)
          · exact rangeBounds 3599 513 h6 (by omega) (by omega)
        have hge : workStart + 257 ≤ w := hbounds.1
        have hupper : w < workStart + localWorkSize := by
          rw [hlocalSizeEq]
          exact hbounds.2
        refine ⟨hge, ?_⟩
        rw [pointAddWork]
        apply List.mem_append_left
        apply List.mem_range'_1.mpr
        exact
          ⟨(Nat.le_add_right workStart 257).trans hge,
            hupper⟩
      · have hshifted :
            ∃ a ∈ Secp256k1Instance.secpLayout.allWires,
              pointAddArithmeticOffset workStart + a = w := by
          simpa only [pointAddArithmeticWork, shiftWires,
            List.mem_map] using harithmetic
        rcases hshifted with ⟨a, ha, rfl⟩
        refine ⟨?_, ?_⟩
        · rw [pointAddArithmeticOffset]
          exact
            (Nat.add_le_add_left hlocalSize workStart).trans
              (Nat.le_add_right (workStart + localWorkSize) a)
        · rw [pointAddWork]
          exact List.mem_append_right _ harithmetic

  have hremainingClean :
      Clean
        (pointAddY workStart ++
          pointAddFlagWork workStart ++
          pointAddBranchWork workStart)
        (Classical.run (pointAddCopyX pointReg workStart) st) := by
    intro w hw
    have hwFacts := hremainingFacts w hw
    have hwGe : workStart + 257 ≤ w := hwFacts.1
    have hwNotDst : w ∉ (pointAddX workStart).take 256 := by
      intro hdst
      rw [hdstEq] at hdst
      have hbounds : workStart ≤ w ∧ w < workStart + 256 :=
        List.mem_range'_1.mp hdst
      have hwLt : w < workStart + 257 :=
        hbounds.2.trans_le
          (Nat.add_le_add_left (by omega : 256 ≤ 257) workStart)
      exact (Nat.not_lt_of_ge hwGe) hwLt
    rw [hother w hwNotDst]
    exact hclean w hwFacts.2

  exact ⟨hpointAgree, hxValue, hremainingClean⟩

theorem pointAddCopyY_correct
    (pointReg outReg : List Wire)
    (workStart : Wire)
    (st : BasisState)
    (hpointLength : pointReg.length = pointWidth)
    (hnodup :
      (pointReg ++ outReg ++ pointAddWork workStart).Nodup)
    (hclean :
      Clean
        (pointAddY workStart ++
         pointAddFlagWork workStart ++
         pointAddBranchWork workStart)
        st) :
    let after :=
      Classical.run (pointAddCopyY pointReg workStart) st
    AgreesOn pointReg st after ∧
      regValue (pointAddX workStart) after =
        regValue (pointAddX workStart) st ∧
      regValue (pointAddY workStart) after =
        regValue (PointRegister.y pointReg) st ∧
      Clean (pointAddFlagWork workStart) after ∧
      Clean (pointAddBranchWork workStart) after := by
  dsimp

  have hlocalSizeEq : localWorkSize = 4112 := by
    norm_num [localWorkSize, selectedOffset, candidateOffset, flagOffset,
      yHistoryOffset, yDifferenceOffset, xHistoryOffset,
      xDifferenceOffset, zeroHistoryOffset, constOffset, fieldAreaSize,
      fieldWidth, Secp256k1Instance.fieldWidth, pointWidth]

  have hdstEq :
      (pointAddY workStart).take 256 =
        List.range' (workStart + 257) 256 := by
    simp [pointAddY, fieldWidth, Secp256k1Instance.fieldWidth,
      List.take_range'_of_length_ge]

  have hdstWork :
      ∀ w ∈ (pointAddY workStart).take 256,
        w ∈ pointAddWork workStart := by
    intro w hw
    rw [hdstEq] at hw
    have hbounds := List.mem_range'_1.mp hw
    rw [pointAddWork]
    apply List.mem_append_left
    apply List.mem_range'_1.mpr
    refine ⟨by omega, ?_⟩
    rw [hlocalSizeEq]
    omega

  have hdstY :
      ∀ w ∈ (pointAddY workStart).take 256,
        w ∈ pointAddY workStart := by
    intro w hw
    exact List.mem_of_mem_take hw

  have hsrcMem :
      ∀ w ∈ PointRegister.y pointReg, w ∈ pointReg := by
    intro w hw
    change w ∈ (pointReg.drop 257).take 256 at hw
    exact List.mem_of_mem_drop (List.mem_of_mem_take hw)

  obtain ⟨hpublicNodup, _hworkNodup, hpublicWork⟩ :=
    List.nodup_append.mp hnodup
  obtain ⟨hpointNodup, _houtNodup, _hpointOut⟩ :=
    List.nodup_append.mp hpublicNodup

  have hsrcNodup : (PointRegister.y pointReg).Nodup := by
    apply List.Nodup.sublist
      ((List.take_sublist 256 (pointReg.drop 257)).trans
        (List.drop_sublist 257 pointReg))
    exact hpointNodup

  have hdstNodup : ((pointAddY workStart).take 256).Nodup := by
    rw [hdstEq]
    exact List.nodup_range'

  have hcopyNodup :
      (PointRegister.y pointReg ++
        (pointAddY workStart).take 256).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hsrcNodup, hdstNodup, ?_⟩
    intro a ha b hb
    exact hpublicWork a
      (List.mem_append_left outReg (hsrcMem a ha))
      b (hdstWork b hb)

  have hdstClean :
      Clean ((pointAddY workStart).take 256) st := by
    apply Arithmetic.Clean.mono hclean
    intro w hw
    exact List.mem_append_left _
      (List.mem_append_left _ (hdstY w hw))

  have hcopyValue :
      regValue ((pointAddY workStart).take 256)
          (Classical.run (pointAddCopyY pointReg workStart) st) =
        regValue (PointRegister.y pointReg) st := by
    simpa only [pointAddCopyY] using
      (Arithmetic.copyReg_correct
        (PointRegister.y pointReg)
        ((pointAddY workStart).take 256)
        st
        (by
          rw [hdstEq]
          simpa using
            (PointRegister.y_length pointReg hpointLength).symm)
        hcopyNodup hdstClean)

  have hother (w : Wire)
      (hw : w ∉ (pointAddY workStart).take 256) :
      Classical.run (pointAddCopyY pointReg workStart) st w = st w := by
    simpa only [pointAddCopyY] using
      (Arithmetic.copyReg_other w
        (PointRegister.y pointReg)
        ((pointAddY workStart).take 256) st hw)

  have hpointAgree :
      AgreesOn pointReg st
        (Classical.run (pointAddCopyY pointReg workStart) st) := by
    intro w hw
    apply hother
    intro hdst
    exact
      (hpublicWork w (List.mem_append_left outReg hw)
        w (hdstWork w hdst)) rfl

  have hxAgree :
      AgreesOn (pointAddX workStart) st
        (Classical.run (pointAddCopyY pointReg workStart) st) := by
    intro w hx
    apply hother
    intro hdst
    have hxBounds : workStart ≤ w ∧ w < workStart + 257 := by
      simpa [pointAddX, fieldWidth,
        Secp256k1Instance.fieldWidth] using
        (List.mem_range'_1.mp hx)
    rw [hdstEq] at hdst
    have hdstBounds := List.mem_range'_1.mp hdst
    exact (Nat.not_lt_of_ge hdstBounds.1) hxBounds.2

  have hxValue :
      regValue (pointAddX workStart)
          (Classical.run (pointAddCopyY pointReg workStart) st) =
        regValue (pointAddX workStart) st :=
    Arithmetic.AgreesOn.regValue hxAgree

  have hhighNotDst :
      workStart + 513 ∉ (pointAddY workStart).take 256 := by
    rw [hdstEq]
    simp [List.mem_range'_1]

  have hhighY : workStart + 513 ∈ pointAddY workStart := by
    simp [pointAddY, fieldWidth, Secp256k1Instance.fieldWidth,
      List.mem_range'_1]

  have hhighClean :
      Clean [workStart + 513]
        (Classical.run (pointAddCopyY pointReg workStart) st) := by
    intro w hw
    simp only [List.mem_singleton] at hw
    subst w
    rw [hother (workStart + 513) hhighNotDst]
    exact hclean (workStart + 513)
      (List.mem_append_left _
        (List.mem_append_left _ hhighY))

  have hpointAddYShape :
      pointAddY workStart =
        PointRegister.padCoordinate
          ((pointAddY workStart).take 256)
          (workStart + 513) := by
    rw [PointRegister.padCoordinate, hdstEq]
    change
      List.range' (workStart + 257) 257 =
        List.range' (workStart + 257) 256 ++
          [workStart + 513]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (List.range'_concat
        (s := workStart + 257) (n := 256) (step := 1))

  have hyValue :
      regValue (pointAddY workStart)
          (Classical.run (pointAddCopyY pointReg workStart) st) =
        regValue (PointRegister.y pointReg) st := by
    rw [hpointAddYShape]
    exact
      (PointRegister.regValue_padCoordinate_of_clean
        ((pointAddY workStart).take 256)
        (workStart + 513)
        (Classical.run (pointAddCopyY pointReg workStart) st)
        hhighClean).trans hcopyValue

  have rangeLower
      (offset len : Nat)
      {w : Wire}
      (hw : workStart + offset ≤ w ∧
        w < workStart + offset + len)
      (hmin : 514 ≤ offset) :
      workStart + 514 ≤ w :=
    (Nat.add_le_add_left hmin workStart).trans hw.1

  have wireLower
      (offset : Nat)
      {w : Wire}
      (hw : w = workStart + offset)
      (hmin : 514 ≤ offset) :
      workStart + 514 ≤ w := by
    subst w
    exact Nat.add_le_add_left hmin workStart

  have hflagLower :
      ∀ w ∈ pointAddFlagWork workStart,
        workStart + 514 ≤ w := by
    intro w hflag
    simp only [pointAddFlagWork, pointAddConst,
      pointAddZeroHistory, pointAddXDifference,
      pointAddXHistory, pointAddYDifference,
      pointAddYHistory, pointAddInfinityFlag,
      pointAddXEqFlag, pointAddYNegFlag,
      pointAddGenericFlag, pointAddPairFlag,
      pointAddDoubleFlag, List.mem_append,
      List.mem_cons, List.mem_range'_1] at hflag
    norm_num [flagOffset, yHistoryOffset, yDifferenceOffset,
      xHistoryOffset, xDifferenceOffset, zeroHistoryOffset,
      constOffset, fieldAreaSize, fieldWidth,
      Secp256k1Instance.fieldWidth] at hflag
    rcases hflag with
        (((((h0 | h1) | h2) | h3) | h4) | h5) |
          (h6 | h7 | h8 | h9 | h10 | h11)
    · exact rangeLower 1799 256 h0 (by omega)
    · exact wireLower 2055 h1 (by omega)
    · exact rangeLower 2056 256 h2 (by omega)
    · exact rangeLower 2312 256 h3 (by omega)
    · exact rangeLower 2568 256 h4 (by omega)
    · exact rangeLower 2824 256 h5 (by omega)
    · exact wireLower 3080 h6 (by omega)
    · exact wireLower 3081 h7 (by omega)
    · exact wireLower 3082 h8 (by omega)
    · exact wireLower 3083 h9 (by omega)
    · exact wireLower 3084 h10 (by omega)
    · exact wireLower 3085 h11 (by omega)

  have hbranchLower :
      ∀ w ∈ pointAddBranchWork workStart,
        workStart + 514 ≤ w := by
    intro w hbranch
    rcases List.mem_append.mp hbranch with hlocal | harithmetic
    · simp only [pointAddT0, pointAddT1,
        pointAddT2, pointAddT3, pointAddT4,
        pointAddCandidate, pointAddSelected,
        List.mem_append, List.mem_range'_1] at hlocal
      norm_num [selectedOffset, candidateOffset,
        flagOffset, yHistoryOffset, yDifferenceOffset,
        xHistoryOffset, xDifferenceOffset, zeroHistoryOffset,
        constOffset, fieldAreaSize, fieldWidth,
        Secp256k1Instance.fieldWidth, pointWidth] at hlocal
      rcases hlocal with
          (((((h0 | h1) | h2) | h3) | h4) | h5) | h6
      · exact rangeLower 514 257 h0 (by omega)
      · exact rangeLower 771 257 h1 (by omega)
      · exact rangeLower 1028 257 h2 (by omega)
      · exact rangeLower 1285 257 h3 (by omega)
      · exact rangeLower 1542 257 h4 (by omega)
      · exact rangeLower 3086 513 h5 (by omega)
      · exact rangeLower 3599 513 h6 (by omega)
    · have hshifted :
          ∃ a ∈ Secp256k1Instance.secpLayout.allWires,
            pointAddArithmeticOffset workStart + a = w := by
        simpa only [pointAddArithmeticWork, shiftWires,
          List.mem_map] using harithmetic
      rcases hshifted with ⟨a, _ha, rfl⟩
      rw [pointAddArithmeticOffset, hlocalSizeEq]
      exact
        (Nat.add_le_add_left (by omega : 514 ≤ 4112) workStart).trans
          (Nat.le_add_right (workStart + 4112) a)

  have hnotDstOfLower (w : Wire)
      (hlower : workStart + 514 ≤ w) :
      w ∉ (pointAddY workStart).take 256 := by
    intro hdst
    rw [hdstEq] at hdst
    have hdstBounds :
        workStart + 257 ≤ w ∧ w < workStart + 257 + 256 :=
      List.mem_range'_1.mp hdst
    have hdstUpper : w < workStart + 514 := by
      exact hdstBounds.2.trans_le
        (Nat.add_le_add_left (by omega : 257 + 256 ≤ 514) workStart)
    exact (Nat.not_lt_of_ge hlower) hdstUpper

  have hflagClean :
      Clean (pointAddFlagWork workStart)
        (Classical.run (pointAddCopyY pointReg workStart) st) := by
    intro w hw
    rw [hother w (hnotDstOfLower w (hflagLower w hw))]
    exact hclean w
      (List.mem_append_left _ (List.mem_append_right _ hw))

  have hbranchClean :
      Clean (pointAddBranchWork workStart)
        (Classical.run (pointAddCopyY pointReg workStart) st) := by
    intro w hw
    rw [hother w (hnotDstOfLower w (hbranchLower w hw))]
    exact hclean w (List.mem_append_right _ hw)

  exact ⟨hpointAgree, hxValue, hyValue, hflagClean, hbranchClean⟩

theorem pointAddCoordinateCopies_correct
    (pointReg outReg : List Wire)
    (workStart : Wire)
    (st : BasisState)
    (hpointLength : pointReg.length = pointWidth)
    (hnodup :
      (pointReg ++ outReg ++ pointAddWork workStart).Nodup)
    (hclean :
      Clean (pointAddWork workStart) st) :
    let after :=
      Classical.run
        (pointAddCoordinateCopies pointReg workStart)
        st
    AgreesOn pointReg st after ∧
      regValue (pointAddX workStart) after =
        regValue (PointRegister.x pointReg) st ∧
      regValue (pointAddY workStart) after =
        regValue (PointRegister.y pointReg) st ∧
      Clean (pointAddFlagWork workStart) after ∧
      Clean (pointAddBranchWork workStart) after := by
  dsimp
  rw [pointAddCoordinateCopies, Classical.run_append]

  let mid :=
    Classical.run (pointAddCopyX pointReg workStart) st

  have hx :=
    pointAddCopyX_correct
      pointReg outReg workStart st
      hpointLength hnodup hclean

  change
    AgreesOn pointReg st mid ∧
      regValue (pointAddX workStart) mid =
        regValue (PointRegister.x pointReg) st ∧
      Clean
        (pointAddY workStart ++
         pointAddFlagWork workStart ++
         pointAddBranchWork workStart)
        mid
    at hx

  rcases hx with ⟨hpointX, hxValue, hcleanAfterX⟩

  have hy :=
    pointAddCopyY_correct
      pointReg outReg workStart mid
      hpointLength hnodup hcleanAfterX

  let after :=
    Classical.run (pointAddCopyY pointReg workStart) mid

  change
    AgreesOn pointReg mid after ∧
      regValue (pointAddX workStart) after =
        regValue (pointAddX workStart) mid ∧
      regValue (pointAddY workStart) after =
        regValue (PointRegister.y pointReg) mid ∧
      Clean (pointAddFlagWork workStart) after ∧
      Clean (pointAddBranchWork workStart) after
    at hy

  rcases hy with
    ⟨hpointY, hxKeep, hyValue, hflagClean, hbranchClean⟩

  have hpointFinal : AgreesOn pointReg st after := by
    intro w hw
    calc
      after w = mid w := hpointY w hw
      _ = st w := hpointX w hw

  have hyPublic :
      regValue (PointRegister.y pointReg) mid =
        regValue (PointRegister.y pointReg) st := by
    exact Arithmetic.AgreesOn.regValue
      (fun w hw => hpointX w (by
        rw [← PointRegister.tag_x_y pointReg hpointLength]
        simp [hw]))

  change
    AgreesOn pointReg st after ∧
      regValue (pointAddX workStart) after =
        regValue (PointRegister.x pointReg) st ∧
      regValue (pointAddY workStart) after =
        regValue (PointRegister.y pointReg) st ∧
      Clean (pointAddFlagWork workStart) after ∧
      Clean (pointAddBranchWork workStart) after

  refine ⟨hpointFinal, ?_, ?_, hflagClean, hbranchClean⟩
  · exact hxKeep.trans hxValue
  · exact hyValue.trans hyPublic

private theorem pointAddFlags_usesOnly
    (pointReg : List Wire)
    (workStart : Wire)
    (xC yC : Fp) :
    CircuitUsesOnly
      (pointReg ++ pointAddFlagWork workStart)
      (pointAddFlags pointReg workStart xC yC) := by
  simp only [pointAddFlags]
  have htag :
      ∀ w ∈ PointRegister.tag pointReg,
        w ∈ pointReg ++ pointAddFlagWork workStart := by
    intro w hw
    exact List.mem_append_left _ (List.mem_of_mem_take hw)
  have hx :
      ∀ w ∈ PointRegister.x pointReg,
        w ∈ pointReg ++ pointAddFlagWork workStart := by
    intro w hw
    apply List.mem_append_left
    exact List.mem_of_mem_drop (List.mem_of_mem_take hw)
  have hy :
      ∀ w ∈ PointRegister.y pointReg,
        w ∈ pointReg ++ pointAddFlagWork workStart := by
    intro w hw
    apply List.mem_append_left
    exact List.mem_of_mem_drop (List.mem_of_mem_take hw)
  have hflag :
      ∀ w ∈ pointAddFlagWork workStart,
        w ∈ pointReg ++ pointAddFlagWork workStart := by
    intro w hw
    exact List.mem_append_right _ hw
  have hconst :
      ∀ w ∈ pointAddConst workStart,
        w ∈ pointReg ++ pointAddFlagWork workStart := by
    intro w hw
    apply hflag
    simp [pointAddFlagWork, hw]
  have hzero :
      ∀ w ∈ pointAddZeroHistory workStart,
        w ∈ pointReg ++ pointAddFlagWork workStart := by
    intro w hw
    apply hflag
    simp [pointAddFlagWork, hw]
  have hxdifference :
      ∀ w ∈ pointAddXDifference workStart,
        w ∈ pointReg ++ pointAddFlagWork workStart := by
    intro w hw
    apply hflag
    simp [pointAddFlagWork, hw]
  have hxhistory :
      ∀ w ∈ pointAddXHistory workStart,
        w ∈ pointReg ++ pointAddFlagWork workStart := by
    intro w hw
    apply hflag
    simp [pointAddFlagWork, hw]
  have hydifference :
      ∀ w ∈ pointAddYDifference workStart,
        w ∈ pointReg ++ pointAddFlagWork workStart := by
    intro w hw
    apply hflag
    simp [pointAddFlagWork, hw]
  have hyhistory :
      ∀ w ∈ pointAddYHistory workStart,
        w ∈ pointReg ++ pointAddFlagWork workStart := by
    intro w hw
    apply hflag
    simp [pointAddFlagWork, hw]

  have hzeroFlag :
      CircuitUsesOnly
        (pointReg ++ pointAddFlagWork workStart)
        (zeroFlag
          (PointRegister.tag pointReg)
          (pointAddInfinityFlag workStart)
          (pointAddZeroHistory workStart)) := by
    apply usesOnly_mono (zeroFlag_usesOnly _ _ _)
    intro w hw
    simp only [zeroFlagWires, List.mem_append,
      List.mem_cons] at hw
    rcases hw with htagMem | hflagMem | hhistoryMem
    · exact htag w htagMem
    · subst w
      apply hflag
      simp [pointAddFlagWork]
    · exact hzero w hhistoryMem

  have hequalX :
      CircuitUsesOnly
        (pointReg ++ pointAddFlagWork workStart)
        (equalFlag
          (PointRegister.x pointReg)
          (pointAddConst workStart)
          (pointAddXEqFlag workStart)
          (pointAddXDifference workStart)
          (pointAddXHistory workStart)) := by
    apply usesOnly_mono (equalFlag_usesOnly _ _ _ _ _)
    intro w hw
    simp only [equalFlagWires, List.mem_append,
      List.mem_cons] at hw
    rcases hw with ((hxMem | hconstMem) | hdiffMem) |
        hflagMem | hhistoryMem
    · exact hx w hxMem
    · exact hconst w hconstMem
    · exact hxdifference w hdiffMem
    · subst w
      apply hflag
      simp [pointAddFlagWork]
    · exact hxhistory w hhistoryMem

  have hequalY :
      CircuitUsesOnly
        (pointReg ++ pointAddFlagWork workStart)
        (equalFlag
          (PointRegister.y pointReg)
          (pointAddConst workStart)
          (pointAddYNegFlag workStart)
          (pointAddYDifference workStart)
          (pointAddYHistory workStart)) := by
    apply usesOnly_mono (equalFlag_usesOnly _ _ _ _ _)
    intro w hw
    simp only [equalFlagWires, List.mem_append,
      List.mem_cons] at hw
    rcases hw with ((hyMem | hconstMem) | hdiffMem) |
        hflagMem | hhistoryMem
    · exact hy w hyMem
    · exact hconst w hconstMem
    · exact hydifference w hdiffMem
    · subst w
      apply hflag
      simp [pointAddFlagWork]
    · exact hyhistory w hhistoryMem

  have hloadX :
      CircuitUsesOnly
        (pointReg ++ pointAddFlagWork workStart)
        (loadConst (pointAddConst workStart) xC.val) :=
    usesOnly_mono (loadConst_usesOnly _ _) hconst

  have hloadY :
      CircuitUsesOnly
        (pointReg ++ pointAddFlagWork workStart)
        (loadConst (pointAddConst workStart) (-yC).val) :=
    usesOnly_mono (loadConst_usesOnly _ _) hconst

  have hgates :
      CircuitUsesOnly
        (pointReg ++ pointAddFlagWork workStart)
        ([Gate.X (pointAddInfinityFlag workStart),
          Gate.X (pointAddXEqFlag workStart),
          Gate.CCX
            (pointAddInfinityFlag workStart)
            (pointAddXEqFlag workStart)
            (pointAddGenericFlag workStart),
          Gate.X (pointAddXEqFlag workStart),
          Gate.X (pointAddInfinityFlag workStart),
          Gate.X (pointAddYNegFlag workStart),
          Gate.CCX
            (pointAddXEqFlag workStart)
            (pointAddYNegFlag workStart)
            (pointAddPairFlag workStart),
          Gate.X (pointAddYNegFlag workStart),
          Gate.X (pointAddInfinityFlag workStart),
          Gate.CCX
            (pointAddInfinityFlag workStart)
            (pointAddPairFlag workStart)
            (pointAddDoubleFlag workStart),
          Gate.X (pointAddInfinityFlag workStart)] : Circuit) := by
    simp [CircuitUsesOnly, Gate.UsesOnly,
      pointAddFlagWork]

  have hprefix1 := usesOnly_append hzeroFlag hloadX
  have hprefix2 := usesOnly_append hprefix1 hequalX
  have hprefix3 := usesOnly_append hprefix2 hloadX
  have hprefix4 := usesOnly_append hprefix3 hloadY
  have hprefix5 := usesOnly_append hprefix4 hequalY
  have hprefix6 := usesOnly_append hprefix5 hloadY
  exact usesOnly_append hprefix6 hgates

private theorem pointAddXEqualWork_nodup
    (workStart : Wire) :
    ((pointAddConst workStart ++
        pointAddXDifference workStart) ++
      pointAddXEqFlag workStart ::
        pointAddXHistory workStart).Nodup := by
  simp [pointAddConst, pointAddXDifference,
    pointAddXEqFlag, pointAddXHistory,
    List.nodup_append, List.nodup_range',
    constOffset, xDifferenceOffset, xHistoryOffset,
    zeroHistoryOffset, flagOffset, yHistoryOffset,
    yDifferenceOffset, fieldAreaSize, fieldWidth,
    Secp256k1Instance.fieldWidth]
  constructor
  · intro a haLower haUpper
    constructor
    · intro h
      subst a
      omega
    · intro b hbLower hbUpper h
      subst b
      omega
  · intro a haLower haUpper b hb
    rcases hb with hb | hb | hb
    · intro h
      subst b
      omega
    · subst b
      intro h
      subst a
      omega
    · intro h
      subst b
      omega

private theorem pointAddYEqualWork_nodup
    (workStart : Wire) :
    ((pointAddConst workStart ++
        pointAddYDifference workStart) ++
      pointAddYNegFlag workStart ::
        pointAddYHistory workStart).Nodup := by
  simp [pointAddConst, pointAddYDifference,
    pointAddYNegFlag, pointAddYHistory,
    List.nodup_append, List.nodup_range',
    constOffset, yDifferenceOffset, yHistoryOffset,
    xHistoryOffset, xDifferenceOffset, zeroHistoryOffset,
    flagOffset, fieldAreaSize, fieldWidth,
    Secp256k1Instance.fieldWidth]
  constructor
  · intro a haLower haUpper
    constructor
    · intro h
      subst a
      omega
    · intro b hbLower hbUpper h
      subst b
      omega
  · intro a haLower haUpper b hb
    rcases hb with hb | hb | hb
    · intro h
      subst b
      omega
    · subst b
      intro h
      subst a
      omega
    · intro h
      subst b
      omega

private theorem pointAddZeroFlagWork_nodup
    (workStart : Wire) :
    (pointAddInfinityFlag workStart ::
      pointAddZeroHistory workStart).Nodup := by
  simp [pointAddInfinityFlag, pointAddZeroHistory,
    flagOffset, yHistoryOffset, yDifferenceOffset,
    xHistoryOffset, xDifferenceOffset, zeroHistoryOffset,
    constOffset, fieldAreaSize, fieldWidth,
    Secp256k1Instance.fieldWidth]

private theorem run_loadConst_twice
    (ws : List Wire) (c : Nat) (st : BasisState)
    (hnd : ws.Nodup) :
    Classical.run (loadConst ws c)
        (Classical.run (loadConst ws c) st) = st := by
  induction ws generalizing c st with
  | nil =>
      simp [loadConst]
  | cons w ws ih =>
      obtain ⟨hw, hws⟩ := List.nodup_cons.mp hnd
      rw [loadConst]
      by_cases hc : c % 2 = 1
      · rw [if_pos hc]
        simp only [Classical.run_append,
          Classical.run_cons, Classical.run_nil]
        have hcomm (s : BasisState) :
            Classical.applyGate (Gate.X w)
                (Classical.run (loadConst ws (c / 2)) s) =
              Classical.run (loadConst ws (c / 2))
                (Classical.applyGate (Gate.X w) s) := by
          funext v
          by_cases hvw : v = w
          · subst v
            simp only [Classical.applyGate]
            rw [loadConst_other w ws (c / 2) s hw,
              loadConst_other w ws (c / 2)
                (s[w ↦ !s w]) hw]
            simp [upd]
          · by_cases hv : v ∈ ws
            · have hcongr :=
                CircuitUsesOnly.run_congr
                  (loadConst_usesOnly ws (c / 2))
                  (st₁ := s)
                  (st₂ := Classical.applyGate (Gate.X w) s)
                  (by
                    intro a ha
                    simp only [Classical.applyGate]
                    exact (upd_other s w (!s w)
                      (fun e => hw (e ▸ ha))).symm)
                  v hv
              simp only [Classical.applyGate]
              rw [upd_other _ _ _ hvw]
              exact hcongr
            · simp only [Classical.applyGate]
              rw [upd_other _ _ _ hvw,
                loadConst_other v ws (c / 2) s hv,
                loadConst_other v ws (c / 2)
                  (s[w ↦ !s w]) hv]
              rw [upd_other _ _ _ hvw]
        rw [hcomm]
        rw [ih (c / 2) _ hws]
        funext v
        by_cases hv : v = w <;>
          simp [Classical.applyGate, upd, hv]
      · rw [if_neg hc]
        simpa using ih (c / 2) st hws

private theorem offset_lt_le_false
    (start w leftEnd rightStart : Nat)
    (hupper : w < start + leftEnd)
    (hlower : start + rightStart ≤ w)
    (hgap : leftEnd ≤ rightStart) : False := by
  omega

private theorem offset_ne
    (start left right : Nat)
    (hne : left ≠ right) :
    start + left ≠ start + right := by
  omega

theorem pointAddFlags_semantics
    (pointReg outReg : List Wire)
    (workStart : Wire)
    {xC yC : Fp}
    (st : BasisState)
    (hpointLength : pointReg.length = pointWidth)
    (hnodup :
      (pointReg ++ outReg ++ pointAddWork workStart).Nodup)
    (hcleanFlags :
      Clean (pointAddFlagWork workStart) st)
    (hcleanBranch :
      Clean (pointAddBranchWork workStart) st) :
    let after :=
      Classical.run
        (pointAddFlags pointReg workStart xC yC)
        st
    AgreesOn pointReg st after ∧
      regValue (pointAddX workStart) after =
        regValue (pointAddX workStart) st ∧
      regValue (pointAddY workStart) after =
        regValue (pointAddY workStart) st ∧
      after (pointAddInfinityFlag workStart) =
        decide (regValue (PointRegister.tag pointReg) st = 0) ∧
      after (pointAddGenericFlag workStart) =
        decide (
          regValue (PointRegister.tag pointReg) st ≠ 0 ∧
          regValue (PointRegister.x pointReg) st ≠ xC.val) ∧
      after (pointAddDoubleFlag workStart) =
        decide (
          regValue (PointRegister.tag pointReg) st ≠ 0 ∧
          regValue (PointRegister.x pointReg) st = xC.val ∧
          regValue (PointRegister.y pointReg) st ≠ (-yC).val) ∧
      Clean (pointAddBranchWork workStart) after := by
  dsimp

  have hlocalSizeEq : localWorkSize = 4112 := by
    norm_num [localWorkSize, selectedOffset, candidateOffset,
      flagOffset, yHistoryOffset, yDifferenceOffset,
      xHistoryOffset, xDifferenceOffset, zeroHistoryOffset,
      constOffset, fieldAreaSize, fieldWidth,
      Secp256k1Instance.fieldWidth, pointWidth]

  obtain ⟨hpublicNodup, _hworkNodup, hpublicWork⟩ :=
    List.nodup_append.mp hnodup
  obtain ⟨hpointNodup, _houtNodup, _hpointOut⟩ :=
    List.nodup_append.mp hpublicNodup

  have hpointWork :
      ∀ a ∈ pointReg, ∀ b ∈ pointAddWork workStart,
        a ≠ b := by
    intro a ha b hb hEq
    exact hpublicWork a
      (List.mem_append_left outReg ha) b hb hEq

  have hflagWorkSubset :
      ∀ w ∈ pointAddFlagWork workStart,
        w ∈ pointAddWork workStart := by
    intro w hw
    rw [pointAddWork]
    apply List.mem_append_left
    apply List.mem_range'_1.mpr
    rw [hlocalSizeEq]
    simp only [pointAddFlagWork, pointAddConst,
      pointAddZeroHistory, pointAddXDifference,
      pointAddXHistory, pointAddYDifference,
      pointAddYHistory, pointAddInfinityFlag,
      pointAddXEqFlag, pointAddYNegFlag,
      pointAddGenericFlag, pointAddPairFlag,
      pointAddDoubleFlag, List.mem_append,
      List.mem_cons, List.mem_range'_1] at hw
    norm_num [flagOffset, yHistoryOffset,
      yDifferenceOffset, xHistoryOffset,
      xDifferenceOffset, zeroHistoryOffset,
      constOffset, fieldAreaSize, fieldWidth,
      Secp256k1Instance.fieldWidth] at hw
    rcases hw with
        (((((h0 | h1) | h2) | h3) | h4) | h5) |
          (h6 | h7 | h8 | h9 | h10 | h11)
    · constructor <;> omega
    · subst w
      constructor <;> omega
    · constructor <;> omega
    · constructor <;> omega
    · constructor <;> omega
    · constructor <;> omega
    · subst w
      constructor <;> omega
    · subst w
      constructor <;> omega
    · subst w
      constructor <;> omega
    · subst w
      constructor <;> omega
    · subst w
      constructor <;> omega
    · subst w
      constructor <;> omega

  have htagNodup :
      (PointRegister.tag pointReg).Nodup := by
    apply List.Nodup.sublist (List.take_sublist 1 pointReg)
    exact hpointNodup
  have hxNodup :
      (PointRegister.x pointReg).Nodup := by
    apply List.Nodup.sublist
      ((List.take_sublist 256 (pointReg.drop 1)).trans
        (List.drop_sublist 1 pointReg))
    exact hpointNodup
  have hyNodup :
      (PointRegister.y pointReg).Nodup := by
    apply List.Nodup.sublist
      ((List.take_sublist 256 (pointReg.drop 257)).trans
        (List.drop_sublist 257 pointReg))
    exact hpointNodup

  have hzeroNodup :
      (zeroFlagWires
        (PointRegister.tag pointReg)
        (pointAddInfinityFlag workStart)
        (pointAddZeroHistory workStart)).Nodup := by
    rw [zeroFlagWires]
    apply List.nodup_append.mpr
    refine ⟨htagNodup,
      pointAddZeroFlagWork_nodup workStart, ?_⟩
    intro a ha b hb hEq
    have hbFlagWork : b ∈ pointAddFlagWork workStart := by
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hhistory
      · simp [pointAddFlagWork]
      · simp [pointAddFlagWork, hhistory]
    exact hpointWork a (List.mem_of_mem_take ha) b
      (hflagWorkSubset b hbFlagWork) hEq

  have hxEqualNodup :
      (equalFlagWires
        (PointRegister.x pointReg)
        (pointAddConst workStart)
        (pointAddXEqFlag workStart)
        (pointAddXDifference workStart)
        (pointAddXHistory workStart)).Nodup := by
    have hwork := pointAddXEqualWork_nodup workStart
    have hcombined :
        (PointRegister.x pointReg ++
          ((pointAddConst workStart ++
              pointAddXDifference workStart) ++
            pointAddXEqFlag workStart ::
              pointAddXHistory workStart)).Nodup := by
      apply List.nodup_append.mpr
      refine ⟨hxNodup, hwork, ?_⟩
      intro a ha b hb hEq
      have hbFlagWork : b ∈ pointAddFlagWork workStart := by
        simp only [List.mem_append, List.mem_cons] at hb
        rcases hb with (hconst | hdiff) | hflag | hhistory
        · simp [pointAddFlagWork, hconst]
        · simp [pointAddFlagWork, hdiff]
        · simp [pointAddFlagWork, hflag]
        · simp [pointAddFlagWork, hhistory]
      exact hpointWork a
        (List.mem_of_mem_drop (List.mem_of_mem_take ha)) b
        (hflagWorkSubset b hbFlagWork) hEq
    simpa only [equalFlagWires, List.append_assoc] using hcombined

  have hyEqualNodup :
      (equalFlagWires
        (PointRegister.y pointReg)
        (pointAddConst workStart)
        (pointAddYNegFlag workStart)
        (pointAddYDifference workStart)
        (pointAddYHistory workStart)).Nodup := by
    have hwork := pointAddYEqualWork_nodup workStart
    have hcombined :
        (PointRegister.y pointReg ++
          ((pointAddConst workStart ++
              pointAddYDifference workStart) ++
            pointAddYNegFlag workStart ::
              pointAddYHistory workStart)).Nodup := by
      apply List.nodup_append.mpr
      refine ⟨hyNodup, hwork, ?_⟩
      intro a ha b hb hEq
      have hbFlagWork : b ∈ pointAddFlagWork workStart := by
        simp only [List.mem_append, List.mem_cons] at hb
        rcases hb with (hconst | hdiff) | hflag | hhistory
        · simp [pointAddFlagWork, hconst]
        · simp [pointAddFlagWork, hdiff]
        · simp [pointAddFlagWork, hflag]
        · simp [pointAddFlagWork, hhistory]
      exact hpointWork a
        (List.mem_of_mem_drop (List.mem_of_mem_take ha)) b
        (hflagWorkSubset b hbFlagWork) hEq
    simpa only [equalFlagWires, List.append_assoc] using hcombined

  have hzeroClean :
      Clean
        (pointAddInfinityFlag workStart ::
          pointAddZeroHistory workStart) st := by
    intro w hw
    apply hcleanFlags w
    simp only [List.mem_cons] at hw
    rcases hw with rfl | hw
    · simp [pointAddFlagWork]
    · simp [pointAddFlagWork, hw]

  let afterInfinity :=
    Classical.run
      (zeroFlag
        (PointRegister.tag pointReg)
        (pointAddInfinityFlag workStart)
        (pointAddZeroHistory workStart))
      st

  have hzeroCorrect :
      AgreesOn (PointRegister.tag pointReg) st afterInfinity ∧
        afterInfinity (pointAddInfinityFlag workStart) =
          decide (regValue (PointRegister.tag pointReg) st = 0) ∧
        Clean (pointAddZeroHistory workStart) afterInfinity := by
    simpa [afterInfinity] using
      (zeroFlag_correct
        (PointRegister.tag pointReg)
        (pointAddInfinityFlag workStart)
        (pointAddZeroHistory workStart)
        st
        (by
          simp [pointAddZeroHistory,
            PointRegister.tag_length pointReg hpointLength])
        hzeroNodup hzeroClean)

  have hzeroOtherOfFlag
      (w : Wire)
      (hwFlag : w ∈ pointAddFlagWork workStart)
      (hwInfinity : w ≠ pointAddInfinityFlag workStart)
      (hwHistory : w ∉ pointAddZeroHistory workStart) :
      afterInfinity w = st w := by
    apply
      (zeroFlag_usesOnly
        (PointRegister.tag pointReg)
        (pointAddInfinityFlag workStart)
        (pointAddZeroHistory workStart)).preservesOutside
    simp only [zeroFlagWires, List.mem_append,
      List.mem_cons, not_or]
    refine ⟨?_, hwInfinity, hwHistory⟩
    intro htag
    exact hpointWork w (List.mem_of_mem_take htag) w
      (hflagWorkSubset w hwFlag) rfl

  have hconstCleanAfterInfinity :
      Clean (pointAddConst workStart) afterInfinity := by
    intro w hw
    have hwFlag : w ∈ pointAddFlagWork workStart := by
      simp [pointAddFlagWork, hw]
    rw [hzeroOtherOfFlag w hwFlag]
    · exact hcleanFlags w hwFlag
    · intro h
      subst w
      simp [pointAddConst, List.mem_range'_1,
        pointAddInfinityFlag, flagOffset,
        yHistoryOffset, yDifferenceOffset,
        xHistoryOffset, xDifferenceOffset,
        zeroHistoryOffset, constOffset, fieldAreaSize,
        fieldWidth, Secp256k1Instance.fieldWidth] at hw ;
        omega
    · intro h
      simp [pointAddZeroHistory] at h
      subst w
      simp [pointAddConst, List.mem_range'_1,
        zeroHistoryOffset, constOffset, fieldAreaSize,
        fieldWidth, Secp256k1Instance.fieldWidth] at hw

  have hxScratchCleanAfterInfinity :
      Clean
        (pointAddXEqFlag workStart ::
          pointAddXDifference workStart ++
          pointAddXHistory workStart)
        afterInfinity := by
    intro w hw
    have hwFlag : w ∈ pointAddFlagWork workStart := by
      simp only [List.mem_cons, List.mem_append] at hw
      rcases hw with hprefix | hhistory
      · rcases hprefix with hflag | hdiff
        · simp [pointAddFlagWork, hflag]
        · simp [pointAddFlagWork, hdiff]
      · simp [pointAddFlagWork, hhistory]
    rw [hzeroOtherOfFlag w hwFlag]
    · exact hcleanFlags w hwFlag
    · intro h
      subst w
      simp only [List.mem_cons, List.mem_append] at hw
      rcases hw with hprefix | hhistory
      · rcases hprefix with hflag | hdiff
        · simp [pointAddXEqFlag, pointAddInfinityFlag] at hflag
        · simp [pointAddXDifference, List.mem_range'_1,
            pointAddInfinityFlag, flagOffset,
            yHistoryOffset, yDifferenceOffset,
            xHistoryOffset, xDifferenceOffset,
            zeroHistoryOffset, constOffset, fieldAreaSize,
            fieldWidth, Secp256k1Instance.fieldWidth] at hdiff ;
            omega
      · simp [pointAddXHistory, List.mem_range'_1,
          pointAddInfinityFlag, flagOffset,
          yHistoryOffset, yDifferenceOffset,
          xHistoryOffset, xDifferenceOffset,
          zeroHistoryOffset, constOffset, fieldAreaSize,
          fieldWidth, Secp256k1Instance.fieldWidth] at hhistory ;
          omega
    · intro h
      simp [pointAddZeroHistory] at h
      subst w
      simp only [List.mem_cons, List.mem_append] at hw
      rcases hw with hprefix | hhistory
      · rcases hprefix with hflag | hdiff
        · simp [pointAddXEqFlag, zeroHistoryOffset,
            flagOffset, yHistoryOffset, yDifferenceOffset,
            xHistoryOffset, xDifferenceOffset, constOffset,
            fieldAreaSize, fieldWidth,
            Secp256k1Instance.fieldWidth] at hflag
        · simp [pointAddXDifference, List.mem_range'_1,
            xDifferenceOffset, zeroHistoryOffset,
            constOffset, fieldAreaSize, fieldWidth,
            Secp256k1Instance.fieldWidth] at hdiff
      · simp [pointAddXHistory, List.mem_range'_1,
          xHistoryOffset, xDifferenceOffset,
          zeroHistoryOffset, constOffset, fieldAreaSize,
          fieldWidth, Secp256k1Instance.fieldWidth] at hhistory

  have hconstLength :
      (pointAddConst workStart).length = 256 := by
    simp [pointAddConst]
  have hconstNodup :
      (pointAddConst workStart).Nodup := by
    rw [pointAddConst]
    exact List.nodup_range'

  let afterLoadX :=
    Classical.run
      (loadConst (pointAddConst workStart) xC.val)
      afterInfinity

  have hconstValueAfterLoadX :
      regValue (pointAddConst workStart) afterLoadX = xC.val := by
    apply loadConst_correct
    · exact hconstNodup
    · exact hconstCleanAfterInfinity
    · rw [hconstLength]
      exact xC.val_lt.trans (by norm_num [p])

  have hxScratchCleanAfterLoadX :
      Clean
        (pointAddXEqFlag workStart ::
          pointAddXDifference workStart ++
          pointAddXHistory workStart)
        afterLoadX := by
    intro w hw
    change
      Classical.run
          (loadConst (pointAddConst workStart) xC.val)
          afterInfinity w = false
    rw [loadConst_other w (pointAddConst workStart)
      xC.val afterInfinity]
    · exact hxScratchCleanAfterInfinity w hw
    · intro hconst
      simp only [List.mem_cons, List.mem_append] at hw
      rcases hw with hprefix | hhistory
      · rcases hprefix with hflag | hdiff
        · subst w
          simp [pointAddConst, List.mem_range'_1,
            pointAddXEqFlag, flagOffset,
            yHistoryOffset, yDifferenceOffset,
            xHistoryOffset, xDifferenceOffset,
            zeroHistoryOffset, constOffset, fieldAreaSize,
            fieldWidth, Secp256k1Instance.fieldWidth] at hconst
        · have hconstBounds := List.mem_range'_1.mp hconst
          have hdiffBounds := List.mem_range'_1.mp hdiff
          norm_num [xDifferenceOffset, zeroHistoryOffset,
            constOffset, fieldAreaSize, fieldWidth,
            Secp256k1Instance.fieldWidth] at hconstBounds hdiffBounds
          omega
      · have hconstBounds := List.mem_range'_1.mp hconst
        have hhistoryBounds := List.mem_range'_1.mp hhistory
        norm_num [xHistoryOffset, xDifferenceOffset,
          zeroHistoryOffset, constOffset, fieldAreaSize,
          fieldWidth, Secp256k1Instance.fieldWidth]
          at hconstBounds hhistoryBounds
        omega

  let afterXEq :=
    Classical.run
      (equalFlag
        (PointRegister.x pointReg)
        (pointAddConst workStart)
        (pointAddXEqFlag workStart)
        (pointAddXDifference workStart)
        (pointAddXHistory workStart))
      afterLoadX

  have hxEqualCorrect :
      AgreesOn (PointRegister.x pointReg)
          afterLoadX afterXEq ∧
        AgreesOn (pointAddConst workStart)
          afterLoadX afterXEq ∧
        afterXEq (pointAddXEqFlag workStart) =
          decide (
            regValue (PointRegister.x pointReg) afterLoadX =
              regValue (pointAddConst workStart) afterLoadX) ∧
        Clean
          (pointAddXDifference workStart ++
            pointAddXHistory workStart)
          afterXEq := by
    simpa [afterXEq] using
      (equalFlag_correct
        (PointRegister.x pointReg)
        (pointAddConst workStart)
        (pointAddXEqFlag workStart)
        (pointAddXDifference workStart)
        (pointAddXHistory workStart)
        afterLoadX
        (by
          simp [pointAddConst,
            PointRegister.x_length pointReg hpointLength])
        (by
          simp [pointAddXDifference,
            PointRegister.x_length pointReg hpointLength])
        (by
          simp [pointAddXHistory,
            PointRegister.x_length pointReg hpointLength])
        hxEqualNodup hxScratchCleanAfterLoadX)

  let afterUnloadX :=
    Classical.run
      (loadConst (pointAddConst workStart) xC.val)
      afterXEq

  have hconstCleanAfterUnloadX :
      Clean (pointAddConst workStart) afterUnloadX := by
    intro w hw
    have hcongr :=
      CircuitUsesOnly.run_congr
        (loadConst_usesOnly (pointAddConst workStart) xC.val)
        (st₁ := afterXEq)
        (st₂ := afterLoadX)
        (fun a ha => hxEqualCorrect.2.1 a ha)
        w hw
    change
      Classical.run
          (loadConst (pointAddConst workStart) xC.val)
          afterXEq w = false
    rw [hcongr]
    have htwice :=
      congrFun
        (run_loadConst_twice
          (pointAddConst workStart) xC.val
          afterInfinity hconstNodup) w
    change
      Classical.run
          (loadConst (pointAddConst workStart) xC.val)
          afterLoadX w = false
    rw [htwice]
    exact hconstCleanAfterInfinity w hw

  have hyScratchLocation
      (w : Wire)
      (hw :
        w ∈ pointAddYNegFlag workStart ::
          pointAddYDifference workStart ++
          pointAddYHistory workStart) :
      w = workStart + 3082 ∨
        (workStart + 2568 ≤ w ∧
          w < workStart + 2568 + 256) ∨
        (workStart + 2824 ≤ w ∧
          w < workStart + 2824 + 256) := by
    simp only [List.mem_cons, List.mem_append] at hw
    rcases hw with hprefix | hhistory
    · rcases hprefix with hflag | hdiff
      · left
        simpa [pointAddYNegFlag, flagOffset,
          yHistoryOffset, yDifferenceOffset,
          xHistoryOffset, xDifferenceOffset,
          zeroHistoryOffset, constOffset, fieldAreaSize,
          fieldWidth, Secp256k1Instance.fieldWidth] using hflag
      · right
        left
        simpa [pointAddYDifference, List.mem_range'_1,
          yDifferenceOffset, xHistoryOffset,
          xDifferenceOffset, zeroHistoryOffset,
          constOffset, fieldAreaSize, fieldWidth,
          Secp256k1Instance.fieldWidth] using
          List.mem_range'_1.mp hdiff
    · right
      right
      simpa [pointAddYHistory, List.mem_range'_1,
        yHistoryOffset, yDifferenceOffset,
        xHistoryOffset, xDifferenceOffset,
        zeroHistoryOffset, constOffset, fieldAreaSize,
        fieldWidth, Secp256k1Instance.fieldWidth] using
        List.mem_range'_1.mp hhistory

  have hyScratchFlagWork
      (w : Wire)
      (hw :
        w ∈ pointAddYNegFlag workStart ::
          pointAddYDifference workStart ++
          pointAddYHistory workStart) :
      w ∈ pointAddFlagWork workStart := by
    simp only [List.mem_cons, List.mem_append] at hw
    rcases hw with hprefix | hhistory
    · rcases hprefix with hflag | hdiff
      · simp [pointAddFlagWork, hflag]
      · simp [pointAddFlagWork, hdiff]
    · simp [pointAddFlagWork, hhistory]

  have hyScratchNotConst
      (w : Wire)
      (hw :
        w ∈ pointAddYNegFlag workStart ::
          pointAddYDifference workStart ++
          pointAddYHistory workStart) :
      w ∉ pointAddConst workStart := by
    intro hconst
    have hconstBounds := List.mem_range'_1.mp hconst
    have hloc := hyScratchLocation w hw
    norm_num [pointAddConst, constOffset, fieldAreaSize,
      fieldWidth, Secp256k1Instance.fieldWidth] at hconstBounds
    have hconstUpper : w < workStart + 2055 := by
      simpa [Nat.add_assoc] using hconstBounds.2
    rcases hloc with hflagLoc | hrest
    · exact offset_lt_le_false workStart w 2055 3082
        hconstUpper hflagLoc.ge (by omega)
    · rcases hrest with hdiffLoc | hhistoryLoc
      · rcases hdiffLoc with ⟨hdiffLower, hdiffUpper⟩
        exact offset_lt_le_false workStart w 2055 2568
          hconstUpper hdiffLower (by omega)
      · rcases hhistoryLoc with ⟨hhistoryLower, hhistoryUpper⟩
        exact offset_lt_le_false workStart w 2055 2824
          hconstUpper hhistoryLower (by omega)

  have hyScratchOutsideXEqual
      (w : Wire)
      (hw :
        w ∈ pointAddYNegFlag workStart ::
          pointAddYDifference workStart ++
          pointAddYHistory workStart) :
      w ∉ equalFlagWires
        (PointRegister.x pointReg)
        (pointAddConst workStart)
        (pointAddXEqFlag workStart)
        (pointAddXDifference workStart)
        (pointAddXHistory workStart) := by
    intro hin
    simp only [equalFlagWires, List.mem_append,
      List.mem_cons] at hin
    rcases hin with hprefix | htail
    · rcases hprefix with hlr | hdiff
      · rcases hlr with hx | hconst
        · exact hpointWork w
            (List.mem_of_mem_drop (List.mem_of_mem_take hx)) w
            (hflagWorkSubset w (hyScratchFlagWork w hw)) rfl
        · exact hyScratchNotConst w hw hconst
      · have hdiffBounds := List.mem_range'_1.mp hdiff
        have hloc := hyScratchLocation w hw
        norm_num [pointAddXDifference,
          xDifferenceOffset, zeroHistoryOffset,
          constOffset, fieldAreaSize, fieldWidth,
          Secp256k1Instance.fieldWidth] at hdiffBounds
        have hxDiffUpper : w < workStart + 2312 := by
          simpa [Nat.add_assoc] using hdiffBounds.2
        rcases hloc with hflagLoc | hrest
        · exact offset_lt_le_false workStart w 2312 3082
            hxDiffUpper hflagLoc.ge (by omega)
        · rcases hrest with hdiffLoc | hhistoryLoc
          · rcases hdiffLoc with ⟨hdiffLower, hdiffUpper⟩
            exact offset_lt_le_false workStart w 2312 2568
              hxDiffUpper hdiffLower (by omega)
          · rcases hhistoryLoc with ⟨hhistoryLower, hhistoryUpper⟩
            exact offset_lt_le_false workStart w 2312 2824
              hxDiffUpper hhistoryLower (by omega)
    · rcases htail with hflag | hhistory
      · have hxEq : w = workStart + 3081 := by
          simpa [pointAddXEqFlag, flagOffset,
            yHistoryOffset, yDifferenceOffset,
            xHistoryOffset, xDifferenceOffset,
            zeroHistoryOffset, constOffset, fieldAreaSize,
            fieldWidth, Secp256k1Instance.fieldWidth] using hflag
        have hloc := hyScratchLocation w hw
        rcases hloc with hflagLoc | hrest
        · exact
            (offset_ne workStart 3081 3082 (by omega))
              (hxEq.symm.trans hflagLoc)
        · rcases hrest with hdiffLoc | hhistoryLoc
          · rcases hdiffLoc with ⟨hdiffLower, hdiffUpper⟩
            have hyDiffUpper : w < workStart + 2824 := by
              simpa [Nat.add_assoc] using hdiffUpper
            exact offset_lt_le_false workStart w 2824 3081
              hyDiffUpper hxEq.ge (by omega)
          · rcases hhistoryLoc with ⟨hhistoryLower, hhistoryUpper⟩
            have hyHistoryUpper : w < workStart + 3080 := by
              simpa [Nat.add_assoc] using hhistoryUpper
            exact offset_lt_le_false workStart w 3080 3081
              hyHistoryUpper hxEq.ge (by omega)
      · have hhistoryBounds := List.mem_range'_1.mp hhistory
        have hloc := hyScratchLocation w hw
        norm_num [pointAddXHistory, xHistoryOffset,
          xDifferenceOffset, zeroHistoryOffset,
          constOffset, fieldAreaSize, fieldWidth,
          Secp256k1Instance.fieldWidth] at hhistoryBounds
        have hxHistoryUpper : w < workStart + 2568 := by
          simpa [Nat.add_assoc] using hhistoryBounds.2
        rcases hloc with hflagLoc | hrest
        · exact offset_lt_le_false workStart w 2568 3082
            hxHistoryUpper hflagLoc.ge (by omega)
        · rcases hrest with hdiffLoc | hhistoryLoc
          · rcases hdiffLoc with ⟨hdiffLower, hdiffUpper⟩
            exact offset_lt_le_false workStart w 2568 2568
              hxHistoryUpper hdiffLower (by omega)
          · rcases hhistoryLoc with ⟨hhistoryLower, hhistoryUpper⟩
            exact offset_lt_le_false workStart w 2568 2824
              hxHistoryUpper hhistoryLower (by omega)

  have hyScratchCleanAfterUnloadX :
      Clean
        (pointAddYNegFlag workStart ::
          pointAddYDifference workStart ++
          pointAddYHistory workStart)
        afterUnloadX := by
    intro w hw
    have hwFlag := hyScratchFlagWork w hw
    have hwConst := hyScratchNotConst w hw
    have hloc := hyScratchLocation w hw
    have hwInfinity :
        w ≠ pointAddInfinityFlag workStart := by
      intro h
      have hinfinity : w = workStart + 3080 := by
        simpa [pointAddInfinityFlag, flagOffset,
          yHistoryOffset, yDifferenceOffset,
          xHistoryOffset, xDifferenceOffset,
          zeroHistoryOffset, constOffset, fieldAreaSize,
          fieldWidth, Secp256k1Instance.fieldWidth] using h
      rcases hloc with hflagLoc | hrest
      · exact
          (offset_ne workStart 3080 3082 (by omega))
            (hinfinity.symm.trans hflagLoc)
      · rcases hrest with hdiffLoc | hhistoryLoc
        · rcases hdiffLoc with ⟨hdiffLower, hdiffUpper⟩
          have hyDiffUpper : w < workStart + 2824 := by
            simpa [Nat.add_assoc] using hdiffUpper
          exact offset_lt_le_false workStart w 2824 3080
            hyDiffUpper hinfinity.ge (by omega)
        · rcases hhistoryLoc with ⟨hhistoryLower, hhistoryUpper⟩
          have hyHistoryUpper : w < workStart + 3080 := by
            simpa [Nat.add_assoc] using hhistoryUpper
          exact offset_lt_le_false workStart w 3080 3080
            hyHistoryUpper hinfinity.ge (by omega)
    have hwZeroHistory :
        w ∉ pointAddZeroHistory workStart := by
      intro h
      have hzero : w = workStart + 2055 := by
        simpa [pointAddZeroHistory,
          zeroHistoryOffset, constOffset, fieldAreaSize,
          fieldWidth, Secp256k1Instance.fieldWidth] using h
      rcases hloc with hflagLoc | hrest
      · exact
          (offset_ne workStart 2055 3082 (by omega))
            (hzero.symm.trans hflagLoc)
      · rcases hrest with hdiffLoc | hhistoryLoc
        · rcases hdiffLoc with ⟨hdiffLower, hdiffUpper⟩
          have hzeroUpper : w < workStart + 2568 := by
            rw [hzero]
            exact Nat.add_lt_add_left (by omega) workStart
          exact offset_lt_le_false workStart w 2568 2568
            hzeroUpper hdiffLower (by omega)
        · rcases hhistoryLoc with ⟨hhistoryLower, hhistoryUpper⟩
          have hzeroUpper : w < workStart + 2824 := by
            rw [hzero]
            exact Nat.add_lt_add_left (by omega) workStart
          exact offset_lt_le_false workStart w 2824 2824
            hzeroUpper hhistoryLower (by omega)
    change afterUnloadX w = false
    calc
      afterUnloadX w = afterXEq w := by
        exact loadConst_other w (pointAddConst workStart)
          xC.val afterXEq hwConst
      _ = afterLoadX w := by
        exact
          (equalFlag_usesOnly
            (PointRegister.x pointReg)
            (pointAddConst workStart)
            (pointAddXEqFlag workStart)
            (pointAddXDifference workStart)
            (pointAddXHistory workStart)).preservesOutside
              afterLoadX w (hyScratchOutsideXEqual w hw)
      _ = afterInfinity w := by
        exact loadConst_other w (pointAddConst workStart)
          xC.val afterInfinity hwConst
      _ = st w :=
        hzeroOtherOfFlag w hwFlag hwInfinity hwZeroHistory
      _ = false := hcleanFlags w hwFlag

  let afterLoadY :=
    Classical.run
      (loadConst (pointAddConst workStart) (-yC).val)
      afterUnloadX

  have hconstValueAfterLoadY :
      regValue (pointAddConst workStart) afterLoadY =
        (-yC).val := by
    apply loadConst_correct
    · exact hconstNodup
    · exact hconstCleanAfterUnloadX
    · rw [hconstLength]
      exact (-yC).val_lt.trans (by norm_num [p])

  have hyScratchCleanAfterLoadY :
      Clean
        (pointAddYNegFlag workStart ::
          pointAddYDifference workStart ++
          pointAddYHistory workStart)
        afterLoadY := by
    intro w hw
    change
      Classical.run
          (loadConst (pointAddConst workStart) (-yC).val)
          afterUnloadX w = false
    rw [loadConst_other w (pointAddConst workStart)
      (-yC).val afterUnloadX (hyScratchNotConst w hw)]
    exact hyScratchCleanAfterUnloadX w hw

  let afterYNeg :=
    Classical.run
      (equalFlag
        (PointRegister.y pointReg)
        (pointAddConst workStart)
        (pointAddYNegFlag workStart)
        (pointAddYDifference workStart)
        (pointAddYHistory workStart))
      afterLoadY

  have hyEqualCorrect :
      AgreesOn (PointRegister.y pointReg)
          afterLoadY afterYNeg ∧
        AgreesOn (pointAddConst workStart)
          afterLoadY afterYNeg ∧
        afterYNeg (pointAddYNegFlag workStart) =
          decide (
            regValue (PointRegister.y pointReg) afterLoadY =
              regValue (pointAddConst workStart) afterLoadY) ∧
        Clean
          (pointAddYDifference workStart ++
            pointAddYHistory workStart)
          afterYNeg := by
    simpa [afterYNeg] using
      (equalFlag_correct
        (PointRegister.y pointReg)
        (pointAddConst workStart)
        (pointAddYNegFlag workStart)
        (pointAddYDifference workStart)
        (pointAddYHistory workStart)
        afterLoadY
        (by
          simp [pointAddConst,
            PointRegister.y_length pointReg hpointLength])
        (by
          simp [pointAddYDifference,
            PointRegister.y_length pointReg hpointLength])
        (by
          simp [pointAddYHistory,
            PointRegister.y_length pointReg hpointLength])
        hyEqualNodup hyScratchCleanAfterLoadY)

  let beforeGates :=
    Classical.run
      (loadConst (pointAddConst workStart) (-yC).val)
      afterYNeg

  have hconstCleanBeforeGates :
      Clean (pointAddConst workStart) beforeGates := by
    intro w hw
    have hcongr :=
      CircuitUsesOnly.run_congr
        (loadConst_usesOnly
          (pointAddConst workStart) (-yC).val)
        (st₁ := afterYNeg)
        (st₂ := afterLoadY)
        (fun a ha => hyEqualCorrect.2.1 a ha)
        w hw
    change
      Classical.run
          (loadConst (pointAddConst workStart) (-yC).val)
          afterYNeg w = false
    rw [hcongr]
    have htwice :=
      congrFun
        (run_loadConst_twice
          (pointAddConst workStart) (-yC).val
          afterUnloadX hconstNodup) w
    change
      Classical.run
          (loadConst (pointAddConst workStart) (-yC).val)
          afterLoadY w = false
    rw [htwice]
    exact hconstCleanAfterUnloadX w hw

  have hslicesNodup :=
    PointRegister.tag_x_y_nodup
      pointReg hpointLength hpointNodup
  obtain ⟨htagXNodup, _hyNd, htagXY_Y⟩ :=
    List.nodup_append.mp hslicesNodup
  obtain ⟨_htagNd, _hxNd, htagX⟩ :=
    List.nodup_append.mp htagXNodup

  have hpublicNotConst
      (w : Wire) (hw : w ∈ pointReg) :
      w ∉ pointAddConst workStart := by
    intro hconst
    have hconstFlag :
        w ∈ pointAddFlagWork workStart := by
      simp [pointAddFlagWork, hconst]
    exact hpointWork w hw w
      (hflagWorkSubset w hconstFlag) rfl

  have htagOutsideXEqual
      (w : Wire) (hw : w ∈ PointRegister.tag pointReg) :
      w ∉ equalFlagWires
        (PointRegister.x pointReg)
        (pointAddConst workStart)
        (pointAddXEqFlag workStart)
        (pointAddXDifference workStart)
        (pointAddXHistory workStart) := by
    intro hin
    simp only [equalFlagWires, List.mem_append,
      List.mem_cons] at hin
    rcases hin with hprefix | htail
    · rcases hprefix with hlr | hdiff
      · rcases hlr with hx | hconst
        · exact htagX w hw w hx rfl
        · exact hpublicNotConst w
            (List.mem_of_mem_take hw) hconst
      · have hdiffFlag :
            w ∈ pointAddFlagWork workStart := by
          simp [pointAddFlagWork, hdiff]
        exact hpointWork w (List.mem_of_mem_take hw) w
          (hflagWorkSubset w hdiffFlag) rfl
    · have htailFlag :
          w ∈ pointAddFlagWork workStart := by
        rcases htail with hflag | hhistory
        · simp [pointAddFlagWork, hflag]
        · simp [pointAddFlagWork, hhistory]
      exact hpointWork w (List.mem_of_mem_take hw) w
        (hflagWorkSubset w htailFlag) rfl

  have htagOutsideYEqual
      (w : Wire) (hw : w ∈ PointRegister.tag pointReg) :
      w ∉ equalFlagWires
        (PointRegister.y pointReg)
        (pointAddConst workStart)
        (pointAddYNegFlag workStart)
        (pointAddYDifference workStart)
        (pointAddYHistory workStart) := by
    intro hin
    simp only [equalFlagWires, List.mem_append,
      List.mem_cons] at hin
    rcases hin with hprefix | htail
    · rcases hprefix with hlr | hdiff
      · rcases hlr with hy | hconst
        · exact htagXY_Y w
            (List.mem_append_left _ hw) w hy rfl
        · exact hpublicNotConst w
            (List.mem_of_mem_take hw) hconst
      · have hdiffFlag :
            w ∈ pointAddFlagWork workStart := by
          simp [pointAddFlagWork, hdiff]
        exact hpointWork w (List.mem_of_mem_take hw) w
          (hflagWorkSubset w hdiffFlag) rfl
    · have htailFlag :
          w ∈ pointAddFlagWork workStart := by
        rcases htail with hflag | hhistory
        · simp [pointAddFlagWork, hflag]
        · simp [pointAddFlagWork, hhistory]
      exact hpointWork w (List.mem_of_mem_take hw) w
        (hflagWorkSubset w htailFlag) rfl

  have hxOutsideZero
      (w : Wire) (hw : w ∈ PointRegister.x pointReg) :
      w ∉ zeroFlagWires
        (PointRegister.tag pointReg)
        (pointAddInfinityFlag workStart)
        (pointAddZeroHistory workStart) := by
    intro hin
    simp only [zeroFlagWires, List.mem_append,
      List.mem_cons] at hin
    rcases hin with htag | hflag | hhistory
    · exact htagX w htag w hw rfl
    · have hflagWork :
          w ∈ pointAddFlagWork workStart := by
        simp [pointAddFlagWork, hflag]
      exact hpointWork w
        (List.mem_of_mem_drop (List.mem_of_mem_take hw)) w
        (hflagWorkSubset w hflagWork) rfl
    · have hhistoryWork :
          w ∈ pointAddFlagWork workStart := by
        simp [pointAddFlagWork, hhistory]
      exact hpointWork w
        (List.mem_of_mem_drop (List.mem_of_mem_take hw)) w
        (hflagWorkSubset w hhistoryWork) rfl

  have hyOutsideZero
      (w : Wire) (hw : w ∈ PointRegister.y pointReg) :
      w ∉ zeroFlagWires
        (PointRegister.tag pointReg)
        (pointAddInfinityFlag workStart)
        (pointAddZeroHistory workStart) := by
    intro hin
    simp only [zeroFlagWires, List.mem_append,
      List.mem_cons] at hin
    rcases hin with htag | hflag | hhistory
    · exact htagXY_Y w
        (List.mem_append_left _ htag) w hw rfl
    · have hflagWork :
          w ∈ pointAddFlagWork workStart := by
        simp [pointAddFlagWork, hflag]
      exact hpointWork w
        (List.mem_of_mem_drop (List.mem_of_mem_take hw)) w
        (hflagWorkSubset w hflagWork) rfl
    · have hhistoryWork :
          w ∈ pointAddFlagWork workStart := by
        simp [pointAddFlagWork, hhistory]
      exact hpointWork w
        (List.mem_of_mem_drop (List.mem_of_mem_take hw)) w
        (hflagWorkSubset w hhistoryWork) rfl

  have hxOutsideYEqual
      (w : Wire) (hw : w ∈ PointRegister.x pointReg) :
      w ∉ equalFlagWires
        (PointRegister.y pointReg)
        (pointAddConst workStart)
        (pointAddYNegFlag workStart)
        (pointAddYDifference workStart)
        (pointAddYHistory workStart) := by
    intro hin
    simp only [equalFlagWires, List.mem_append,
      List.mem_cons] at hin
    rcases hin with hprefix | htail
    · rcases hprefix with hlr | hdiff
      · rcases hlr with hy | hconst
        · exact htagXY_Y w
            (List.mem_append_right _ hw) w hy rfl
        · exact hpublicNotConst w
            (List.mem_of_mem_drop (List.mem_of_mem_take hw))
            hconst
      · have hdiffFlag :
            w ∈ pointAddFlagWork workStart := by
          simp [pointAddFlagWork, hdiff]
        exact hpointWork w
          (List.mem_of_mem_drop (List.mem_of_mem_take hw)) w
          (hflagWorkSubset w hdiffFlag) rfl
    · have htailFlag :
          w ∈ pointAddFlagWork workStart := by
        rcases htail with hflag | hhistory
        · simp [pointAddFlagWork, hflag]
        · simp [pointAddFlagWork, hhistory]
      exact hpointWork w
        (List.mem_of_mem_drop (List.mem_of_mem_take hw)) w
        (hflagWorkSubset w htailFlag) rfl

  have hyOutsideXEqual
      (w : Wire) (hw : w ∈ PointRegister.y pointReg) :
      w ∉ equalFlagWires
        (PointRegister.x pointReg)
        (pointAddConst workStart)
        (pointAddXEqFlag workStart)
        (pointAddXDifference workStart)
        (pointAddXHistory workStart) := by
    intro hin
    simp only [equalFlagWires, List.mem_append,
      List.mem_cons] at hin
    rcases hin with hprefix | htail
    · rcases hprefix with hlr | hdiff
      · rcases hlr with hx | hconst
        · exact htagXY_Y w
            (List.mem_append_right _ hx) w hw rfl
        · exact hpublicNotConst w
            (List.mem_of_mem_drop (List.mem_of_mem_take hw))
            hconst
      · have hdiffFlag :
            w ∈ pointAddFlagWork workStart := by
          simp [pointAddFlagWork, hdiff]
        exact hpointWork w
          (List.mem_of_mem_drop (List.mem_of_mem_take hw)) w
          (hflagWorkSubset w hdiffFlag) rfl
    · have htailFlag :
          w ∈ pointAddFlagWork workStart := by
        rcases htail with hflag | hhistory
        · simp [pointAddFlagWork, hflag]
        · simp [pointAddFlagWork, hhistory]
      exact hpointWork w
        (List.mem_of_mem_drop (List.mem_of_mem_take hw)) w
        (hflagWorkSubset w htailFlag) rfl

  have htagBeforeGates :
      AgreesOn (PointRegister.tag pointReg) st beforeGates := by
    intro w hw
    have hwPoint := List.mem_of_mem_take hw
    have hwConst := hpublicNotConst w hwPoint
    calc
      beforeGates w = afterYNeg w :=
        loadConst_other w (pointAddConst workStart)
          (-yC).val afterYNeg hwConst
      _ = afterLoadY w :=
        (equalFlag_usesOnly
          (PointRegister.y pointReg)
          (pointAddConst workStart)
          (pointAddYNegFlag workStart)
          (pointAddYDifference workStart)
          (pointAddYHistory workStart)).preservesOutside
            afterLoadY w (htagOutsideYEqual w hw)
      _ = afterUnloadX w :=
        loadConst_other w (pointAddConst workStart)
          (-yC).val afterUnloadX hwConst
      _ = afterXEq w :=
        loadConst_other w (pointAddConst workStart)
          xC.val afterXEq hwConst
      _ = afterLoadX w :=
        (equalFlag_usesOnly
          (PointRegister.x pointReg)
          (pointAddConst workStart)
          (pointAddXEqFlag workStart)
          (pointAddXDifference workStart)
          (pointAddXHistory workStart)).preservesOutside
            afterLoadX w (htagOutsideXEqual w hw)
      _ = afterInfinity w :=
        loadConst_other w (pointAddConst workStart)
          xC.val afterInfinity hwConst
      _ = st w := hzeroCorrect.1 w hw

  have hxBeforeGates :
      AgreesOn (PointRegister.x pointReg) st beforeGates := by
    intro w hw
    have hwPoint :=
      List.mem_of_mem_drop (List.mem_of_mem_take hw)
    have hwConst := hpublicNotConst w hwPoint
    calc
      beforeGates w = afterYNeg w :=
        loadConst_other w (pointAddConst workStart)
          (-yC).val afterYNeg hwConst
      _ = afterLoadY w :=
        (equalFlag_usesOnly
          (PointRegister.y pointReg)
          (pointAddConst workStart)
          (pointAddYNegFlag workStart)
          (pointAddYDifference workStart)
          (pointAddYHistory workStart)).preservesOutside
            afterLoadY w (hxOutsideYEqual w hw)
      _ = afterUnloadX w :=
        loadConst_other w (pointAddConst workStart)
          (-yC).val afterUnloadX hwConst
      _ = afterXEq w :=
        loadConst_other w (pointAddConst workStart)
          xC.val afterXEq hwConst
      _ = afterLoadX w := hxEqualCorrect.1 w hw
      _ = afterInfinity w :=
        loadConst_other w (pointAddConst workStart)
          xC.val afterInfinity hwConst
      _ = st w :=
        (zeroFlag_usesOnly
          (PointRegister.tag pointReg)
          (pointAddInfinityFlag workStart)
          (pointAddZeroHistory workStart)).preservesOutside
            st w (hxOutsideZero w hw)

  have hyBeforeGates :
      AgreesOn (PointRegister.y pointReg) st beforeGates := by
    intro w hw
    have hwPoint :=
      List.mem_of_mem_drop (List.mem_of_mem_take hw)
    have hwConst := hpublicNotConst w hwPoint
    calc
      beforeGates w = afterYNeg w :=
        loadConst_other w (pointAddConst workStart)
          (-yC).val afterYNeg hwConst
      _ = afterLoadY w := hyEqualCorrect.1 w hw
      _ = afterUnloadX w :=
        loadConst_other w (pointAddConst workStart)
          (-yC).val afterUnloadX hwConst
      _ = afterXEq w :=
        loadConst_other w (pointAddConst workStart)
          xC.val afterXEq hwConst
      _ = afterLoadX w :=
        (equalFlag_usesOnly
          (PointRegister.x pointReg)
          (pointAddConst workStart)
          (pointAddXEqFlag workStart)
          (pointAddXDifference workStart)
          (pointAddXHistory workStart)).preservesOutside
            afterLoadX w (hyOutsideXEqual w hw)
      _ = afterInfinity w :=
        loadConst_other w (pointAddConst workStart)
          xC.val afterInfinity hwConst
      _ = st w :=
        (zeroFlag_usesOnly
          (PointRegister.tag pointReg)
          (pointAddInfinityFlag workStart)
          (pointAddZeroHistory workStart)).preservesOutside
            st w (hyOutsideZero w hw)

  have hhighFlagNotConst
      (w : Wire)
      (hlower : workStart + 3080 ≤ w) :
      w ∉ pointAddConst workStart := by
    intro hconst
    have hbounds := List.mem_range'_1.mp hconst
    norm_num [pointAddConst, constOffset, fieldAreaSize,
      fieldWidth, Secp256k1Instance.fieldWidth] at hbounds
    have hupper : w < workStart + 2055 := by
      simpa [Nat.add_assoc] using hbounds.2
    exact offset_lt_le_false workStart w 2055 3080
      hupper hlower (by omega)

  have hhighFlagOutsideXEqual
      (w : Wire)
      (hwFlag : w ∈ pointAddFlagWork workStart)
      (hlower : workStart + 3080 ≤ w)
      (hnotXEq : w ≠ pointAddXEqFlag workStart) :
      w ∉ equalFlagWires
        (PointRegister.x pointReg)
        (pointAddConst workStart)
        (pointAddXEqFlag workStart)
        (pointAddXDifference workStart)
        (pointAddXHistory workStart) := by
    intro hin
    simp only [equalFlagWires, List.mem_append,
      List.mem_cons] at hin
    rcases hin with hprefix | htail
    · rcases hprefix with hlr | hdiff
      · rcases hlr with hx | hconst
        · exact hpointWork w
            (List.mem_of_mem_drop (List.mem_of_mem_take hx)) w
            (hflagWorkSubset w hwFlag) rfl
        · exact hhighFlagNotConst w hlower hconst
      · have hbounds := List.mem_range'_1.mp hdiff
        norm_num [pointAddXDifference,
          xDifferenceOffset, zeroHistoryOffset,
          constOffset, fieldAreaSize, fieldWidth,
          Secp256k1Instance.fieldWidth] at hbounds
        have hupper : w < workStart + 2312 := by
          simpa [Nat.add_assoc] using hbounds.2
        exact offset_lt_le_false workStart w 2312 3080
          hupper hlower (by omega)
    · rcases htail with hflag | hhistory
      · exact hnotXEq hflag
      · have hbounds := List.mem_range'_1.mp hhistory
        norm_num [pointAddXHistory, xHistoryOffset,
          xDifferenceOffset, zeroHistoryOffset,
          constOffset, fieldAreaSize, fieldWidth,
          Secp256k1Instance.fieldWidth] at hbounds
        have hupper : w < workStart + 2568 := by
          simpa [Nat.add_assoc] using hbounds.2
        exact offset_lt_le_false workStart w 2568 3080
          hupper hlower (by omega)

  have hhighFlagOutsideYEqual
      (w : Wire)
      (hwFlag : w ∈ pointAddFlagWork workStart)
      (hlower : workStart + 3080 ≤ w)
      (hnotYNeg : w ≠ pointAddYNegFlag workStart) :
      w ∉ equalFlagWires
        (PointRegister.y pointReg)
        (pointAddConst workStart)
        (pointAddYNegFlag workStart)
        (pointAddYDifference workStart)
        (pointAddYHistory workStart) := by
    intro hin
    simp only [equalFlagWires, List.mem_append,
      List.mem_cons] at hin
    rcases hin with hprefix | htail
    · rcases hprefix with hlr | hdiff
      · rcases hlr with hy | hconst
        · exact hpointWork w
            (List.mem_of_mem_drop (List.mem_of_mem_take hy)) w
            (hflagWorkSubset w hwFlag) rfl
        · exact hhighFlagNotConst w hlower hconst
      · have hbounds := List.mem_range'_1.mp hdiff
        norm_num [pointAddYDifference,
          yDifferenceOffset, xHistoryOffset,
          xDifferenceOffset, zeroHistoryOffset,
          constOffset, fieldAreaSize, fieldWidth,
          Secp256k1Instance.fieldWidth] at hbounds
        have hupper : w < workStart + 2824 := by
          simpa [Nat.add_assoc] using hbounds.2
        exact offset_lt_le_false workStart w 2824 3080
          hupper hlower (by omega)
    · rcases htail with hflag | hhistory
      · exact hnotYNeg hflag
      · have hbounds := List.mem_range'_1.mp hhistory
        norm_num [pointAddYHistory, yHistoryOffset,
          yDifferenceOffset, xHistoryOffset,
          xDifferenceOffset, zeroHistoryOffset,
          constOffset, fieldAreaSize, fieldWidth,
          Secp256k1Instance.fieldWidth] at hbounds
        have hupper : w < workStart + 3080 := by
          simpa [Nat.add_assoc] using hbounds.2
        exact offset_lt_le_false workStart w 3080 3080
          hupper hlower (by omega)

  have hprefixOtherHighFlag
      (w : Wire)
      (hwFlag : w ∈ pointAddFlagWork workStart)
      (hlower : workStart + 3080 ≤ w)
      (hwInfinity : w ≠ pointAddInfinityFlag workStart)
      (hwXEq : w ≠ pointAddXEqFlag workStart)
      (hwYNeg : w ≠ pointAddYNegFlag workStart) :
      beforeGates w = st w := by
    have hwConst := hhighFlagNotConst w hlower
    have hwZeroHistory :
        w ∉ pointAddZeroHistory workStart := by
      intro hzero
      have hzeroEq : w = workStart + 2055 := by
        simpa [pointAddZeroHistory, zeroHistoryOffset,
          constOffset, fieldAreaSize, fieldWidth,
          Secp256k1Instance.fieldWidth] using hzero
      have hupper : w < workStart + 3080 := by
        rw [hzeroEq]
        exact Nat.add_lt_add_left (by omega) workStart
      exact offset_lt_le_false workStart w 3080 3080
        hupper hlower (by omega)
    calc
      beforeGates w = afterYNeg w :=
        loadConst_other w (pointAddConst workStart)
          (-yC).val afterYNeg hwConst
      _ = afterLoadY w :=
        (equalFlag_usesOnly
          (PointRegister.y pointReg)
          (pointAddConst workStart)
          (pointAddYNegFlag workStart)
          (pointAddYDifference workStart)
          (pointAddYHistory workStart)).preservesOutside
            afterLoadY w
              (hhighFlagOutsideYEqual w hwFlag hlower hwYNeg)
      _ = afterUnloadX w :=
        loadConst_other w (pointAddConst workStart)
          (-yC).val afterUnloadX hwConst
      _ = afterXEq w :=
        loadConst_other w (pointAddConst workStart)
          xC.val afterXEq hwConst
      _ = afterLoadX w :=
        (equalFlag_usesOnly
          (PointRegister.x pointReg)
          (pointAddConst workStart)
          (pointAddXEqFlag workStart)
          (pointAddXDifference workStart)
          (pointAddXHistory workStart)).preservesOutside
            afterLoadX w
              (hhighFlagOutsideXEqual w hwFlag hlower hwXEq)
      _ = afterInfinity w :=
        loadConst_other w (pointAddConst workStart)
          xC.val afterInfinity hwConst
      _ = st w :=
        hzeroOtherOfFlag w hwFlag hwInfinity hwZeroHistory

  have hinfinityFlagMem :
      pointAddInfinityFlag workStart ∈
        pointAddFlagWork workStart := by
    simp [pointAddFlagWork]

  have hinfinityFlagLower :
      workStart + 3080 ≤
        pointAddInfinityFlag workStart := by
    simp [pointAddInfinityFlag, flagOffset,
      yHistoryOffset, yDifferenceOffset,
      xHistoryOffset, xDifferenceOffset,
      zeroHistoryOffset, constOffset, fieldAreaSize,
      fieldWidth, Secp256k1Instance.fieldWidth]

  have hxEqFlagMem :
      pointAddXEqFlag workStart ∈
        pointAddFlagWork workStart := by
    simp [pointAddFlagWork]

  have hxEqFlagLower :
      workStart + 3080 ≤ pointAddXEqFlag workStart := by
    simp [pointAddXEqFlag, flagOffset,
      yHistoryOffset, yDifferenceOffset,
      xHistoryOffset, xDifferenceOffset,
      zeroHistoryOffset, constOffset, fieldAreaSize,
      fieldWidth, Secp256k1Instance.fieldWidth]

  have hyNegFlagMem :
      pointAddYNegFlag workStart ∈
        pointAddFlagWork workStart := by
    simp [pointAddFlagWork]

  have hyNegFlagLower :
      workStart + 3080 ≤ pointAddYNegFlag workStart := by
    simp [pointAddYNegFlag, flagOffset,
      yHistoryOffset, yDifferenceOffset,
      xHistoryOffset, xDifferenceOffset,
      zeroHistoryOffset, constOffset, fieldAreaSize,
      fieldWidth, Secp256k1Instance.fieldWidth]

  have hinfinityNeXEq :
      pointAddInfinityFlag workStart ≠
        pointAddXEqFlag workStart := by
    simp [pointAddInfinityFlag, pointAddXEqFlag]

  have hinfinityNeYNeg :
      pointAddInfinityFlag workStart ≠
        pointAddYNegFlag workStart := by
    simp [pointAddInfinityFlag, pointAddYNegFlag]

  have hxEqNeYNeg :
      pointAddXEqFlag workStart ≠
        pointAddYNegFlag workStart := by
    simp [pointAddXEqFlag, pointAddYNegFlag]

  have hinfinityBeforeGates :
      beforeGates (pointAddInfinityFlag workStart) =
        decide (regValue (PointRegister.tag pointReg) st = 0) := by
    have hnotConst :=
      hhighFlagNotConst
        (pointAddInfinityFlag workStart)
        hinfinityFlagLower
    calc
      beforeGates (pointAddInfinityFlag workStart) =
          afterYNeg (pointAddInfinityFlag workStart) :=
        loadConst_other _ (pointAddConst workStart)
          (-yC).val afterYNeg hnotConst
      _ = afterLoadY (pointAddInfinityFlag workStart) :=
        (equalFlag_usesOnly
          (PointRegister.y pointReg)
          (pointAddConst workStart)
          (pointAddYNegFlag workStart)
          (pointAddYDifference workStart)
          (pointAddYHistory workStart)).preservesOutside
            afterLoadY _
              (hhighFlagOutsideYEqual _ hinfinityFlagMem
                hinfinityFlagLower hinfinityNeYNeg)
      _ = afterUnloadX (pointAddInfinityFlag workStart) :=
        loadConst_other _ (pointAddConst workStart)
          (-yC).val afterUnloadX hnotConst
      _ = afterXEq (pointAddInfinityFlag workStart) :=
        loadConst_other _ (pointAddConst workStart)
          xC.val afterXEq hnotConst
      _ = afterLoadX (pointAddInfinityFlag workStart) :=
        (equalFlag_usesOnly
          (PointRegister.x pointReg)
          (pointAddConst workStart)
          (pointAddXEqFlag workStart)
          (pointAddXDifference workStart)
          (pointAddXHistory workStart)).preservesOutside
            afterLoadX _
              (hhighFlagOutsideXEqual _ hinfinityFlagMem
                hinfinityFlagLower hinfinityNeXEq)
      _ = afterInfinity (pointAddInfinityFlag workStart) :=
        loadConst_other _ (pointAddConst workStart)
          xC.val afterInfinity hnotConst
      _ = decide
          (regValue (PointRegister.tag pointReg) st = 0) :=
        hzeroCorrect.2.1

  have hxAfterLoadX :
      regValue (PointRegister.x pointReg) afterLoadX =
        regValue (PointRegister.x pointReg) st := by
    apply Arithmetic.AgreesOn.regValue
    intro w hw
    have hwPoint :=
      List.mem_of_mem_drop (List.mem_of_mem_take hw)
    calc
      afterLoadX w = afterInfinity w :=
        loadConst_other w (pointAddConst workStart)
          xC.val afterInfinity (hpublicNotConst w hwPoint)
      _ = st w :=
        (zeroFlag_usesOnly
          (PointRegister.tag pointReg)
          (pointAddInfinityFlag workStart)
          (pointAddZeroHistory workStart)).preservesOutside
            st w (hxOutsideZero w hw)

  have hxEqBeforeGates :
      beforeGates (pointAddXEqFlag workStart) =
        decide
          (regValue (PointRegister.x pointReg) st = xC.val) := by
    have hnotConst :=
      hhighFlagNotConst
        (pointAddXEqFlag workStart) hxEqFlagLower
    calc
      beforeGates (pointAddXEqFlag workStart) =
          afterYNeg (pointAddXEqFlag workStart) :=
        loadConst_other _ (pointAddConst workStart)
          (-yC).val afterYNeg hnotConst
      _ = afterLoadY (pointAddXEqFlag workStart) :=
        (equalFlag_usesOnly
          (PointRegister.y pointReg)
          (pointAddConst workStart)
          (pointAddYNegFlag workStart)
          (pointAddYDifference workStart)
          (pointAddYHistory workStart)).preservesOutside
            afterLoadY _
              (hhighFlagOutsideYEqual _ hxEqFlagMem
                hxEqFlagLower hxEqNeYNeg)
      _ = afterUnloadX (pointAddXEqFlag workStart) :=
        loadConst_other _ (pointAddConst workStart)
          (-yC).val afterUnloadX hnotConst
      _ = afterXEq (pointAddXEqFlag workStart) :=
        loadConst_other _ (pointAddConst workStart)
          xC.val afterXEq hnotConst
      _ = decide
          (regValue (PointRegister.x pointReg) afterLoadX =
            regValue (pointAddConst workStart) afterLoadX) :=
        hxEqualCorrect.2.2.1
      _ = decide
          (regValue (PointRegister.x pointReg) st = xC.val) := by
        rw [hxAfterLoadX, hconstValueAfterLoadX]

  have hyAfterLoadY :
      regValue (PointRegister.y pointReg) afterLoadY =
        regValue (PointRegister.y pointReg) st := by
    have hbeforeUnloadY :
        AgreesOn (PointRegister.y pointReg)
          afterYNeg beforeGates := by
      intro w hw
      exact loadConst_other w (pointAddConst workStart)
        (-yC).val afterYNeg
        (hpublicNotConst w
          (List.mem_of_mem_drop (List.mem_of_mem_take hw)))
    calc
      regValue (PointRegister.y pointReg) afterLoadY =
          regValue (PointRegister.y pointReg) afterYNeg :=
        (Arithmetic.AgreesOn.regValue hyEqualCorrect.1).symm
      _ = regValue (PointRegister.y pointReg) beforeGates :=
        (Arithmetic.AgreesOn.regValue hbeforeUnloadY).symm
      _ = regValue (PointRegister.y pointReg) st :=
        Arithmetic.AgreesOn.regValue hyBeforeGates

  have hyNegBeforeGates :
      beforeGates (pointAddYNegFlag workStart) =
        decide
          (regValue (PointRegister.y pointReg) st = (-yC).val) := by
    have hnotConst :=
      hhighFlagNotConst
        (pointAddYNegFlag workStart) hyNegFlagLower
    calc
      beforeGates (pointAddYNegFlag workStart) =
          afterYNeg (pointAddYNegFlag workStart) :=
        loadConst_other _ (pointAddConst workStart)
          (-yC).val afterYNeg hnotConst
      _ = decide
          (regValue (PointRegister.y pointReg) afterLoadY =
            regValue (pointAddConst workStart) afterLoadY) :=
        hyEqualCorrect.2.2.1
      _ = decide
          (regValue (PointRegister.y pointReg) st = (-yC).val) := by
        rw [hyAfterLoadY, hconstValueAfterLoadY]

  have hgenericFlagMem :
      pointAddGenericFlag workStart ∈
        pointAddFlagWork workStart := by
    simp [pointAddFlagWork]

  have hgenericFlagLower :
      workStart + 3080 ≤
        pointAddGenericFlag workStart := by
    simp [pointAddGenericFlag, flagOffset,
      yHistoryOffset, yDifferenceOffset,
      xHistoryOffset, xDifferenceOffset,
      zeroHistoryOffset, constOffset, fieldAreaSize,
      fieldWidth, Secp256k1Instance.fieldWidth]

  have hgenericBeforeGates :
      beforeGates (pointAddGenericFlag workStart) = false := by
    rw [hprefixOtherHighFlag
      (pointAddGenericFlag workStart)
      hgenericFlagMem hgenericFlagLower]
    · exact hcleanFlags _ hgenericFlagMem
    · simp [pointAddGenericFlag, pointAddInfinityFlag]
    · simp [pointAddGenericFlag, pointAddXEqFlag]
    · simp [pointAddGenericFlag, pointAddYNegFlag]

  have hpairFlagMem :
      pointAddPairFlag workStart ∈
        pointAddFlagWork workStart := by
    simp [pointAddFlagWork]

  have hpairFlagLower :
      workStart + 3080 ≤ pointAddPairFlag workStart := by
    simp [pointAddPairFlag, flagOffset,
      yHistoryOffset, yDifferenceOffset,
      xHistoryOffset, xDifferenceOffset,
      zeroHistoryOffset, constOffset, fieldAreaSize,
      fieldWidth, Secp256k1Instance.fieldWidth]

  have hpairBeforeGates :
      beforeGates (pointAddPairFlag workStart) = false := by
    rw [hprefixOtherHighFlag
      (pointAddPairFlag workStart)
      hpairFlagMem hpairFlagLower]
    · exact hcleanFlags _ hpairFlagMem
    · simp [pointAddPairFlag, pointAddInfinityFlag]
    · simp [pointAddPairFlag, pointAddXEqFlag]
    · simp [pointAddPairFlag, pointAddYNegFlag]

  have hdoubleFlagMem :
      pointAddDoubleFlag workStart ∈
        pointAddFlagWork workStart := by
    simp [pointAddFlagWork]

  have hdoubleFlagLower :
      workStart + 3080 ≤
        pointAddDoubleFlag workStart := by
    simp [pointAddDoubleFlag, flagOffset,
      yHistoryOffset, yDifferenceOffset,
      xHistoryOffset, xDifferenceOffset,
      zeroHistoryOffset, constOffset, fieldAreaSize,
      fieldWidth, Secp256k1Instance.fieldWidth]

  have hdoubleBeforeGates :
      beforeGates (pointAddDoubleFlag workStart) = false := by
    rw [hprefixOtherHighFlag
      (pointAddDoubleFlag workStart)
      hdoubleFlagMem hdoubleFlagLower]
    · exact hcleanFlags _ hdoubleFlagMem
    · simp [pointAddDoubleFlag, pointAddInfinityFlag]
    · simp [pointAddDoubleFlag, pointAddXEqFlag]
    · simp [pointAddDoubleFlag, pointAddYNegFlag]

  let manualGates : Circuit :=
    [Gate.X (pointAddInfinityFlag workStart),
      Gate.X (pointAddXEqFlag workStart),
      Gate.CCX
        (pointAddInfinityFlag workStart)
        (pointAddXEqFlag workStart)
        (pointAddGenericFlag workStart),
      Gate.X (pointAddXEqFlag workStart),
      Gate.X (pointAddInfinityFlag workStart),
      Gate.X (pointAddYNegFlag workStart),
      Gate.CCX
        (pointAddXEqFlag workStart)
        (pointAddYNegFlag workStart)
        (pointAddPairFlag workStart),
      Gate.X (pointAddYNegFlag workStart),
      Gate.X (pointAddInfinityFlag workStart),
      Gate.CCX
        (pointAddInfinityFlag workStart)
        (pointAddPairFlag workStart)
        (pointAddDoubleFlag workStart),
      Gate.X (pointAddInfinityFlag workStart)]

  let after := Classical.run manualGates beforeGates

  have hinfinityBeforeGates' :
      beforeGates (workStart + flagOffset) =
        decide (regValue (PointRegister.tag pointReg) st = 0) := by
    simpa only [pointAddInfinityFlag] using
      hinfinityBeforeGates
  have hxEqBeforeGates' :
      beforeGates (workStart + flagOffset + 1) =
        decide
          (regValue (PointRegister.x pointReg) st = xC.val) := by
    simpa only [pointAddXEqFlag] using hxEqBeforeGates
  have hyNegBeforeGates' :
      beforeGates (workStart + flagOffset + 2) =
        decide
          (regValue (PointRegister.y pointReg) st = (-yC).val) := by
    simpa only [pointAddYNegFlag] using hyNegBeforeGates
  have hgenericBeforeGates' :
      beforeGates (workStart + flagOffset + 3) = false := by
    simpa only [pointAddGenericFlag] using hgenericBeforeGates
  have hpairBeforeGates' :
      beforeGates (workStart + flagOffset + 4) = false := by
    simpa only [pointAddPairFlag] using hpairBeforeGates
  have hdoubleBeforeGates' :
      beforeGates (workStart + flagOffset + 5) = false := by
    simpa only [pointAddDoubleFlag] using hdoubleBeforeGates

  have hflagResults :
      after (pointAddInfinityFlag workStart) =
          decide (regValue (PointRegister.tag pointReg) st = 0) ∧
        after (pointAddGenericFlag workStart) =
          decide
            (regValue (PointRegister.tag pointReg) st ≠ 0 ∧
              regValue (PointRegister.x pointReg) st ≠ xC.val) ∧
        after (pointAddDoubleFlag workStart) =
          decide
            (regValue (PointRegister.tag pointReg) st ≠ 0 ∧
              regValue (PointRegister.x pointReg) st = xC.val ∧
              regValue (PointRegister.y pointReg) st ≠ (-yC).val) := by
    by_cases hinfinity :
        regValue (PointRegister.tag pointReg) st = 0 <;>
      by_cases hxEq :
        regValue (PointRegister.x pointReg) st = xC.val <;>
      by_cases hyNeg :
        regValue (PointRegister.y pointReg) st = (-yC).val <;>
      simp [after, manualGates, Classical.run,
        Classical.applyGate, upd,
        pointAddInfinityFlag, pointAddXEqFlag,
        pointAddYNegFlag, pointAddGenericFlag,
        pointAddPairFlag, pointAddDoubleFlag,
        hinfinityBeforeGates', hxEqBeforeGates',
        hyNegBeforeGates', hgenericBeforeGates',
        hpairBeforeGates', hdoubleBeforeGates',
        hinfinity, hxEq, hyNeg]

  have hrun :
      Classical.run
          (pointAddFlags pointReg workStart xC yC) st =
        after := by
    simp [pointAddFlags, after, manualGates,
      beforeGates, afterYNeg, afterLoadY,
      afterUnloadX, afterXEq, afterLoadX,
      afterInfinity, Classical.run_append]

  have hmanualUses :
      CircuitUsesOnly
        (pointAddFlagWork workStart) manualGates := by
    simp [manualGates, CircuitUsesOnly, Gate.UsesOnly,
      pointAddFlagWork]

  have hpointBeforeGates :
      AgreesOn pointReg st beforeGates := by
    intro w hw
    have hwSlices :
        w ∈
          PointRegister.tag pointReg ++
            PointRegister.x pointReg ++
            PointRegister.y pointReg := by
      rw [PointRegister.tag_x_y pointReg hpointLength]
      exact hw
    rcases List.mem_append.mp hwSlices with htagXMem | hy
    · rcases List.mem_append.mp htagXMem with htag | hx
      · exact htagBeforeGates w htag
      · exact hxBeforeGates w hx
    · exact hyBeforeGates w hy

  have hpointAfter : AgreesOn pointReg st after := by
    intro w hw
    calc
      after w = beforeGates w :=
        hmanualUses.preservesOutside beforeGates w (by
          intro hflag
          exact hpointWork w hw w
            (hflagWorkSubset w hflag) rfl)
      _ = st w := hpointBeforeGates w hw

  have rangeInFlagBounds
      (offset len : Nat) {w : Wire}
      (hw : workStart + offset ≤ w ∧
        w < workStart + offset + len)
      (hmin : 1799 ≤ offset)
      (hmax : offset + len ≤ 3086) :
      workStart + 1799 ≤ w ∧
        w < workStart + 3086 := by
    constructor
    · exact (Nat.add_le_add_left hmin workStart).trans hw.1
    · exact hw.2.trans_le (by
        simpa [Nat.add_assoc] using
          Nat.add_le_add_left hmax workStart)

  have wireInFlagBounds
      (offset : Nat) {w : Wire}
      (hw : w = workStart + offset)
      (hmin : 1799 ≤ offset)
      (hmax : offset < 3086) :
      workStart + 1799 ≤ w ∧
        w < workStart + 3086 := by
    subst w
    exact ⟨Nat.add_le_add_left hmin workStart,
      Nat.add_lt_add_left hmax workStart⟩

  have hflagBounds :
      ∀ w ∈ pointAddFlagWork workStart,
        workStart + 1799 ≤ w ∧ w < workStart + 3086 := by
    intro w hw
    simp only [pointAddFlagWork, pointAddConst,
      pointAddZeroHistory, pointAddXDifference,
      pointAddXHistory, pointAddYDifference,
      pointAddYHistory, pointAddInfinityFlag,
      pointAddXEqFlag, pointAddYNegFlag,
      pointAddGenericFlag, pointAddPairFlag,
      pointAddDoubleFlag, List.mem_append,
      List.mem_cons, List.mem_range'_1] at hw
    norm_num [flagOffset, yHistoryOffset,
      yDifferenceOffset, xHistoryOffset,
      xDifferenceOffset, zeroHistoryOffset,
      constOffset, fieldAreaSize, fieldWidth,
      Secp256k1Instance.fieldWidth] at hw
    rcases hw with
        (((((h0 | h1) | h2) | h3) | h4) | h5) |
          (h6 | h7 | h8 | h9 | h10 | h11)
    · exact rangeInFlagBounds 1799 256 h0 (by omega) (by omega)
    · exact wireInFlagBounds 2055 h1 (by omega) (by omega)
    · exact rangeInFlagBounds 2056 256 h2 (by omega) (by omega)
    · exact rangeInFlagBounds 2312 256 h3 (by omega) (by omega)
    · exact rangeInFlagBounds 2568 256 h4 (by omega) (by omega)
    · exact rangeInFlagBounds 2824 256 h5 (by omega) (by omega)
    · exact wireInFlagBounds 3080 h6 (by omega) (by omega)
    · exact wireInFlagBounds 3081 h7 (by omega) (by omega)
    · exact wireInFlagBounds 3082 h8 (by omega) (by omega)
    · exact wireInFlagBounds 3083 h9 (by omega) (by omega)
    · exact wireInFlagBounds 3084 h10 (by omega) (by omega)
    · exact wireInFlagBounds 3085 h11 (by omega) (by omega)

  have hxWorkSubset :
      ∀ w ∈ pointAddX workStart,
        w ∈ pointAddWork workStart := by
    intro w hw
    have hbounds := List.mem_range'_1.mp hw
    rw [pointAddWork]
    apply List.mem_append_left
    apply List.mem_range'_1.mpr
    rw [hlocalSizeEq]
    norm_num [pointAddX, fieldWidth,
      Secp256k1Instance.fieldWidth] at hbounds
    omega

  have hyWorkSubset :
      ∀ w ∈ pointAddY workStart,
        w ∈ pointAddWork workStart := by
    intro w hw
    have hbounds := List.mem_range'_1.mp hw
    rw [pointAddWork]
    apply List.mem_append_left
    apply List.mem_range'_1.mpr
    rw [hlocalSizeEq]
    norm_num [pointAddY, fieldWidth,
      Secp256k1Instance.fieldWidth] at hbounds
    omega

  have hxOutsideFlagFootprint :
      ∀ w ∈ pointAddX workStart,
        w ∉ pointReg ++ pointAddFlagWork workStart := by
    intro w hw hin
    rcases List.mem_append.mp hin with hpoint | hflag
    · exact hpointWork w hpoint w (hxWorkSubset w hw) rfl
    · have hxBounds := List.mem_range'_1.mp hw
      have hflagLower := (hflagBounds w hflag).1
      norm_num [pointAddX, fieldWidth,
        Secp256k1Instance.fieldWidth] at hxBounds
      have hxUpper : w < workStart + 257 := by
        simpa [Nat.add_assoc] using hxBounds.2
      exact offset_lt_le_false workStart w 257 1799
        hxUpper hflagLower (by omega)

  have hyOutsideFlagFootprint :
      ∀ w ∈ pointAddY workStart,
        w ∉ pointReg ++ pointAddFlagWork workStart := by
    intro w hw hin
    rcases List.mem_append.mp hin with hpoint | hflag
    · exact hpointWork w hpoint w (hyWorkSubset w hw) rfl
    · have hyBounds := List.mem_range'_1.mp hw
      have hflagLower := (hflagBounds w hflag).1
      norm_num [pointAddY, fieldWidth,
        Secp256k1Instance.fieldWidth] at hyBounds
      have hyUpper : w < workStart + 514 := by
        simpa [Nat.add_assoc] using hyBounds.2
      exact offset_lt_le_false workStart w 514 1799
        hyUpper hflagLower (by omega)

  have hxAfter :
      regValue (pointAddX workStart) after =
        regValue (pointAddX workStart) st := by
    rw [← hrun]
    apply Arithmetic.AgreesOn.regValue
    intro w hw
    exact
      (pointAddFlags_usesOnly pointReg workStart xC yC).preservesOutside
        st w (hxOutsideFlagFootprint w hw)

  have hyAfter :
      regValue (pointAddY workStart) after =
        regValue (pointAddY workStart) st := by
    rw [← hrun]
    apply Arithmetic.AgreesOn.regValue
    intro w hw
    exact
      (pointAddFlags_usesOnly pointReg workStart xC yC).preservesOutside
        st w (hyOutsideFlagFootprint w hw)

  have localRangeMem
      (offset len : Nat) {w : Wire}
      (hw : workStart + offset ≤ w ∧
        w < workStart + offset + len)
      (hmax : offset + len ≤ 4112) :
      w ∈ List.range' workStart localWorkSize := by
    apply List.mem_range'_1.mpr
    rw [hlocalSizeEq]
    constructor
    · exact (Nat.le_add_right workStart offset).trans hw.1
    · exact hw.2.trans_le (by
        simpa [Nat.add_assoc] using
          Nat.add_le_add_left hmax workStart)

  have hbranchWorkSubset :
      ∀ w ∈ pointAddBranchWork workStart,
        w ∈ pointAddWork workStart := by
    intro w hw
    rw [pointAddBranchWork] at hw
    rcases List.mem_append.mp hw with hlocal | harithmetic
    · rw [pointAddWork]
      apply List.mem_append_left
      simp only [pointAddT0, pointAddT1,
        pointAddT2, pointAddT3, pointAddT4,
        pointAddCandidate, pointAddSelected,
        List.mem_append, List.mem_range'_1] at hlocal
      norm_num [selectedOffset, candidateOffset,
        flagOffset, yHistoryOffset, yDifferenceOffset,
        xHistoryOffset, xDifferenceOffset,
        zeroHistoryOffset, constOffset, fieldAreaSize,
        fieldWidth, Secp256k1Instance.fieldWidth,
        pointWidth] at hlocal
      rcases hlocal with
          (((((h0 | h1) | h2) | h3) | h4) | h5) | h6
      · exact localRangeMem 514 257 h0 (by omega)
      · exact localRangeMem 771 257 h1 (by omega)
      · exact localRangeMem 1028 257 h2 (by omega)
      · exact localRangeMem 1285 257 h3 (by omega)
      · exact localRangeMem 1542 257 h4 (by omega)
      · exact localRangeMem 3086 513 h5 (by omega)
      · exact localRangeMem 3599 513 h6 (by omega)
    · rw [pointAddWork]
      exact List.mem_append_right _ harithmetic

  have hbranchOutsideFlags :
      ∀ w ∈ pointAddBranchWork workStart,
        w ∉ pointAddFlagWork workStart := by
    intro w hw hflag
    have hflagRange := hflagBounds w hflag
    rw [pointAddBranchWork] at hw
    rcases List.mem_append.mp hw with hlocal | harithmetic
    · simp only [pointAddT0, pointAddT1,
        pointAddT2, pointAddT3, pointAddT4,
        pointAddCandidate, pointAddSelected,
        List.mem_append, List.mem_range'_1] at hlocal
      norm_num [selectedOffset, candidateOffset,
        flagOffset, yHistoryOffset, yDifferenceOffset,
        xHistoryOffset, xDifferenceOffset,
        zeroHistoryOffset, constOffset, fieldAreaSize,
        fieldWidth, Secp256k1Instance.fieldWidth,
        pointWidth] at hlocal
      rcases hlocal with
          (((((h0 | h1) | h2) | h3) | h4) | h5) | h6
      · exact offset_lt_le_false workStart w 771 1799
          (by simpa [Nat.add_assoc] using h0.2)
          hflagRange.1 (by omega)
      · exact offset_lt_le_false workStart w 1028 1799
          (by simpa [Nat.add_assoc] using h1.2)
          hflagRange.1 (by omega)
      · exact offset_lt_le_false workStart w 1285 1799
          (by simpa [Nat.add_assoc] using h2.2)
          hflagRange.1 (by omega)
      · exact offset_lt_le_false workStart w 1542 1799
          (by simpa [Nat.add_assoc] using h3.2)
          hflagRange.1 (by omega)
      · exact offset_lt_le_false workStart w 1799 1799
          (by simpa [Nat.add_assoc] using h4.2)
          hflagRange.1 (by omega)
      · exact offset_lt_le_false workStart w 3086 3086
          hflagRange.2 h5.1 (by omega)
      · exact offset_lt_le_false workStart w 3086 3599
          hflagRange.2 h6.1 (by omega)
    · have hshifted :
          ∃ a ∈ Secp256k1Instance.secpLayout.allWires,
            pointAddArithmeticOffset workStart + a = w := by
        simpa only [pointAddArithmeticWork, shiftWires,
          List.mem_map] using harithmetic
      rcases hshifted with ⟨a, _ha, rfl⟩
      have harithmeticLower :
          workStart + 4112 ≤
            pointAddArithmeticOffset workStart + a := by
        rw [pointAddArithmeticOffset, hlocalSizeEq]
        exact Nat.le_add_right (workStart + 4112) a
      exact offset_lt_le_false workStart
        (pointAddArithmeticOffset workStart + a)
        3086 4112 hflagRange.2 harithmeticLower (by omega)

  have hbranchOutsideFlagFootprint :
      ∀ w ∈ pointAddBranchWork workStart,
        w ∉ pointReg ++ pointAddFlagWork workStart := by
    intro w hw hin
    rcases List.mem_append.mp hin with hpoint | hflag
    · exact hpointWork w hpoint w
        (hbranchWorkSubset w hw) rfl
    · exact hbranchOutsideFlags w hw hflag

  have hbranchCleanAfter :
      Clean (pointAddBranchWork workStart) after := by
    intro w hw
    rw [← hrun]
    rw [(pointAddFlags_usesOnly
      pointReg workStart xC yC).preservesOutside
        st w (hbranchOutsideFlagFootprint w hw)]
    exact hcleanBranch w hw

  rw [hrun]
  exact
    ⟨hpointAfter, hxAfter, hyAfter,
      hflagResults.1, hflagResults.2.1,
      hflagResults.2.2, hbranchCleanAfter⟩

/--
If the input is O, setup detects exactly the infinity branch.

The branch workspace remains clean because setup only writes the coordinate
copies and flag/predicate workspace.
-/
theorem pointAddSetup_zero_correct
    [Fact (Nat.Prime p)]
    (pointReg outReg : List Wire)
    (workStart : Wire)
    {xC yC : Fp}
    (st : BasisState)
    (hpointLength :
      pointReg.length = pointWidth)
    (hnodup :
      (pointReg ++ outReg ++ pointAddWork workStart).Nodup)
    (hpoint :
      regValue pointReg st = encodeNat (0 : Point))
    (hclean :
      Clean (pointAddWork workStart) st) :
    let after :=
      Classical.run
        (pointAddSetup pointReg workStart xC yC)
        st
    after (pointAddInfinityFlag workStart) = true ∧
      after (pointAddGenericFlag workStart) = false ∧
      after (pointAddDoubleFlag workStart) = false ∧
      Clean (pointAddBranchWork workStart) after := by
  dsimp
  rw [pointAddSetup, Classical.run_append]

  let copied :=
    Classical.run
      (pointAddCoordinateCopies pointReg workStart)
      st

  have hcopy :
      AgreesOn pointReg st copied ∧
        regValue (pointAddX workStart) copied =
          regValue (PointRegister.x pointReg) st ∧
        regValue (pointAddY workStart) copied =
          regValue (PointRegister.y pointReg) st ∧
        Clean (pointAddFlagWork workStart) copied ∧
        Clean (pointAddBranchWork workStart) copied := by
    simpa [copied] using
      pointAddCoordinateCopies_correct
        pointReg outReg workStart st
        hpointLength hnodup hclean

  rcases hcopy with
    ⟨hpointAgree, _, _, hflagClean, hbranchClean⟩

  have hpointCopied :
      regValue pointReg copied = encodeNat (0 : Point) := by
    calc
      regValue pointReg copied = regValue pointReg st :=
        Arithmetic.AgreesOn.regValue hpointAgree
      _ = encodeNat (0 : Point) := hpoint

  have hslices :=
    PointRegister.slices_of_regValue_zero
      pointReg copied hpointLength hpointCopied

  rcases hslices with ⟨htag, _, _⟩

  let after :=
    Classical.run
      (pointAddFlags pointReg workStart xC yC)
      copied

  have hflags :
      AgreesOn pointReg copied after ∧
        regValue (pointAddX workStart) after =
          regValue (pointAddX workStart) copied ∧
        regValue (pointAddY workStart) after =
          regValue (pointAddY workStart) copied ∧
        after (pointAddInfinityFlag workStart) =
          decide (regValue (PointRegister.tag pointReg) copied = 0) ∧
        after (pointAddGenericFlag workStart) =
          decide (
            regValue (PointRegister.tag pointReg) copied ≠ 0 ∧
            regValue (PointRegister.x pointReg) copied ≠ xC.val) ∧
        after (pointAddDoubleFlag workStart) =
          decide (
            regValue (PointRegister.tag pointReg) copied ≠ 0 ∧
            regValue (PointRegister.x pointReg) copied = xC.val ∧
            regValue (PointRegister.y pointReg) copied ≠ (-yC).val) ∧
        Clean (pointAddBranchWork workStart) after := by
    simpa [after] using
      pointAddFlags_semantics
        pointReg outReg workStart copied
        hpointLength hnodup hflagClean hbranchClean

  rcases hflags with
    ⟨_, _, _, hinfinity, hgeneric, hdouble, hcleanAfter⟩

  change
    after (pointAddInfinityFlag workStart) = true ∧
      after (pointAddGenericFlag workStart) = false ∧
      after (pointAddDoubleFlag workStart) = false ∧
      Clean (pointAddBranchWork workStart) after

  refine ⟨?_, ?_, ?_, hcleanAfter⟩
  · simpa [htag] using hinfinity
  · simpa [htag] using hgeneric
  · simpa [htag] using hdouble

/--
For a finite input R=(xR,yR), setup:

* loads xR and yR into the padded field registers;
* establishes that R is not infinity;
* computes the generic and doubling conditions;
* leaves all branch scratch clean.

The two useful branch predicates are

    generic = (xR ≠ xC)

and

    double = (xR = xC ∧ yR ≠ -yC).
-/
theorem pointAddSetup_some_correct
    [Fact (Nat.Prime p)]
    (pointReg outReg : List Wire)
    (workStart : Wire)
    {xR yR xC yC : Fp}
    (hR : curve.toAffine.Nonsingular xR yR)
    (st : BasisState)
    (hpointLength :
      pointReg.length = pointWidth)
    (hnodup :
      (pointReg ++ outReg ++ pointAddWork workStart).Nodup)
    (hpoint :
      regValue pointReg st = encodeNat (.some hR))
    (hclean :
      Clean (pointAddWork workStart) st) :
    let after :=
      Classical.run
        (pointAddSetup pointReg workStart xC yC)
        st
    regValue (pointAddX workStart) after = xR.val ∧
      regValue (pointAddY workStart) after = yR.val ∧
      after (pointAddInfinityFlag workStart) = false ∧
      after (pointAddGenericFlag workStart) =
        decide (xR ≠ xC) ∧
      after (pointAddDoubleFlag workStart) =
        decide (xR = xC ∧ yR ≠ -yC) ∧
      Clean (pointAddBranchWork workStart) after := by
  letI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩

  dsimp
  rw [pointAddSetup, Classical.run_append]

  let copied :=
    Classical.run
      (pointAddCoordinateCopies pointReg workStart)
      st

  have hcopy :
      AgreesOn pointReg st copied ∧
        regValue (pointAddX workStart) copied =
          regValue (PointRegister.x pointReg) st ∧
        regValue (pointAddY workStart) copied =
          regValue (PointRegister.y pointReg) st ∧
        Clean (pointAddFlagWork workStart) copied ∧
        Clean (pointAddBranchWork workStart) copied := by
    simpa [copied] using
      pointAddCoordinateCopies_correct
        pointReg outReg workStart st
        hpointLength hnodup hclean

  rcases hcopy with
    ⟨hpointAgree, hxCopy, hyCopy, hflagClean, hbranchClean⟩

  have hslicesBefore :=
    PointRegister.slices_of_regValue_some
      pointReg st hR hpointLength hpoint

  rcases hslicesBefore with
    ⟨_, hxBefore, hyBefore⟩

  have hpointCopied :
      regValue pointReg copied = encodeNat (.some hR) := by
    calc
      regValue pointReg copied = regValue pointReg st :=
        Arithmetic.AgreesOn.regValue hpointAgree
      _ = encodeNat (.some hR) := hpoint

  have hslicesCopied :=
    PointRegister.slices_of_regValue_some
      pointReg copied hR hpointLength hpointCopied

  rcases hslicesCopied with
    ⟨htag, hxPublic, hyPublic⟩

  let after :=
    Classical.run
      (pointAddFlags pointReg workStart xC yC)
      copied

  have hflags :
      AgreesOn pointReg copied after ∧
        regValue (pointAddX workStart) after =
          regValue (pointAddX workStart) copied ∧
        regValue (pointAddY workStart) after =
          regValue (pointAddY workStart) copied ∧
        after (pointAddInfinityFlag workStart) =
          decide (regValue (PointRegister.tag pointReg) copied = 0) ∧
        after (pointAddGenericFlag workStart) =
          decide (
            regValue (PointRegister.tag pointReg) copied ≠ 0 ∧
            regValue (PointRegister.x pointReg) copied ≠ xC.val) ∧
        after (pointAddDoubleFlag workStart) =
          decide (
            regValue (PointRegister.tag pointReg) copied ≠ 0 ∧
            regValue (PointRegister.x pointReg) copied = xC.val ∧
            regValue (PointRegister.y pointReg) copied ≠ (-yC).val) ∧
        Clean (pointAddBranchWork workStart) after := by
    simpa [after] using
      pointAddFlags_semantics
        pointReg outReg workStart copied
        hpointLength hnodup hflagClean hbranchClean

  rcases hflags with
    ⟨_, hxKeep, hyKeep,
      hinfinity, hgeneric, hdouble, hcleanAfter⟩

  have hxFinal :
      regValue (pointAddX workStart) after = xR.val := by
    calc
      regValue (pointAddX workStart) after =
          regValue (pointAddX workStart) copied := hxKeep
      _ = regValue (PointRegister.x pointReg) st := hxCopy
      _ = xR.val := hxBefore

  have hyFinal :
      regValue (pointAddY workStart) after = yR.val := by
    calc
      regValue (pointAddY workStart) after =
          regValue (pointAddY workStart) copied := hyKeep
      _ = regValue (PointRegister.y pointReg) st := hyCopy
      _ = yR.val := hyBefore

  have hxVal :
      xR.val = xC.val ↔ xR = xC := by
    constructor
    · intro h
      exact ZMod.val_injective p h
    · intro h
      subst xC
      rfl

  have hyVal :
      yR.val = (-yC).val ↔ yR = -yC := by
    constructor
    · intro h
      exact ZMod.val_injective p h
    · intro h
      subst yR
      rfl

  have hinfinity' :
      after (pointAddInfinityFlag workStart) = false := by
    simpa [htag] using hinfinity

  have hgeneric' :
      after (pointAddGenericFlag workStart) =
        decide (xR ≠ xC) := by
    simpa [htag, hxPublic, hxVal] using hgeneric

  have hdouble' :
      after (pointAddDoubleFlag workStart) =
        decide (xR = xC ∧ yR ≠ -yC) := by
    simpa [htag, hxPublic, hyPublic, hxVal, hyVal] using hdouble

  change
    regValue (pointAddX workStart) after = xR.val ∧
      regValue (pointAddY workStart) after = yR.val ∧
      after (pointAddInfinityFlag workStart) = false ∧
      after (pointAddGenericFlag workStart) =
        decide (xR ≠ xC) ∧
      after (pointAddDoubleFlag workStart) =
        decide (xR = xC ∧ yR ≠ -yC) ∧
      Clean (pointAddBranchWork workStart) after

  exact
    ⟨hxFinal, hyFinal, hinfinity',
      hgeneric', hdouble', hcleanAfter⟩

/--
When only the infinity branch is enabled, the branch stage writes C into
`selected`.

The generic and doubling circuits still execute, but because their controls
are false their candidates are computed and uncomputed without changing
`selected`.
-/
theorem pointAddBranches_infinity_correct
    [Fact (Nat.Prime p)]
    (workStart : Wire)
    {xC yC : Fp}
    (hC : curve.toAffine.Nonsingular xC yC)
    (st : BasisState)
    (hinfinity :
      st (pointAddInfinityFlag workStart) = true)
    (hgeneric :
      st (pointAddGenericFlag workStart) = false)
    (hdouble :
      st (pointAddDoubleFlag workStart) = false)
    (hclean :
      Clean (pointAddBranchWork workStart) st) :
    regValue
        (pointAddSelected workStart)
        (Classical.run
          (pointAddBranches workStart hC)
          st) =
      encodeNat (.some hC) := by
  sorry

/--
When all three branch controls are false, nothing is XORed into `selected`.

Since `selected` starts clean, it stays zero, which is exactly the canonical
encoding of the point at infinity.
-/
theorem pointAddBranches_inverse_correct
    [Fact (Nat.Prime p)]
    (workStart : Wire)
    {xC yC : Fp}
    (hC : curve.toAffine.Nonsingular xC yC)
    (st : BasisState)
    (hinfinity :
      st (pointAddInfinityFlag workStart) = false)
    (hgeneric :
      st (pointAddGenericFlag workStart) = false)
    (hdouble :
      st (pointAddDoubleFlag workStart) = false)
    (hclean :
      Clean (pointAddBranchWork workStart) st) :
    regValue
        (pointAddSelected workStart)
        (Classical.run
          (pointAddBranches workStart hC)
          st) =
      encodeNat (0 : Point) := by
  sorry

/--
When the generic flag is the unique active branch, the branch circuit
computes the generic affine point

    genericAdd hR hC hx

and writes its canonical encoding into `selected`.

This is the lemma that must prove the correctness of
`genericPointCompute`.
-/
theorem pointAddBranches_generic_correct
    [Fact (Nat.Prime p)]
    (workStart : Wire)
    {xR yR xC yC : Fp}
    (hR : curve.toAffine.Nonsingular xR yR)
    (hC : curve.toAffine.Nonsingular xC yC)
    (hx : xR ≠ xC)
    (st : BasisState)
    (hxReg :
      regValue (pointAddX workStart) st = xR.val)
    (hyReg :
      regValue (pointAddY workStart) st = yR.val)
    (hinfinity :
      st (pointAddInfinityFlag workStart) = false)
    (hgeneric :
      st (pointAddGenericFlag workStart) = true)
    (hdouble :
      st (pointAddDoubleFlag workStart) = false)
    (hclean :
      Clean (pointAddBranchWork workStart) st) :
    regValue
        (pointAddSelected workStart)
        (Classical.run
          (pointAddBranches workStart hC)
          st) =
      encodeNat (genericAdd hR hC hx) := by
  sorry

/--
When the doubling flag is the unique active branch, the branch circuit
computes the secp256k1 doubling formulas and writes that point into
`selected`.
-/
theorem pointAddBranches_double_correct
    [Fact (Nat.Prime p)]
    (workStart : Wire)
    {xR yR xC yC : Fp}
    (hR : curve.toAffine.Nonsingular xR yR)
    (hC : curve.toAffine.Nonsingular xC yC)
    (hx : xR = xC)
    (hinv : yR ≠ -yC)
    (st : BasisState)
    (hxReg :
      regValue (pointAddX workStart) st = xR.val)
    (hyReg :
      regValue (pointAddY workStart) st = yR.val)
    (hinfinity :
      st (pointAddInfinityFlag workStart) = false)
    (hgeneric :
      st (pointAddGenericFlag workStart) = false)
    (hdouble :
      st (pointAddDoubleFlag workStart) = true)
    (hclean :
      Clean (pointAddBranchWork workStart) st) :
    regValue
        (pointAddSelected workStart)
        (Classical.run
          (pointAddBranches workStart hC)
          st) =
      encodeNat
        (doublePoint hR
          (self_not_inverse_of_x_eq_of_not_inverse
            hR hC hx hinv)) := by
  sorry

theorem pointAddFiniteCompute_correct
    [Fact (Nat.Prime p)]
    (pointReg outReg : List Wire)
    (workStart : Wire)
    {xC yC : Fp}
    (hC : curve.toAffine.Nonsingular xC yC)
    (R : Point)
    (st : BasisState)
    (hpointLength : pointReg.length = pointWidth)
    (hnodup :
      (pointReg ++ outReg ++ pointAddWork workStart).Nodup)
    (hpoint :
      regValue pointReg st = encodeNat R)
    (hclean :
      Clean (pointAddWork workStart) st) :
    regValue
        (pointAddSelected workStart)
        (Classical.run
          (pointAddFiniteCompute pointReg workStart hC)
          st) =
      encodeNat (affineAdd R (.some hC)) := by

  rw [pointAddFiniteCompute, Classical.run_append]

  let setupState :=
    Classical.run
      (pointAddSetup pointReg workStart xC yC)
      st

  change
    regValue
        (pointAddSelected workStart)
        (Classical.run
          (pointAddBranches workStart hC)
          setupState) =
      encodeNat (affineAdd R (.some hC))

  cases R with

  | zero =>
      have hsetup :=
        pointAddSetup_zero_correct
          pointReg outReg workStart
          (xC := xC) (yC := yC)
          st hpointLength hnodup hpoint hclean

      change
        setupState (pointAddInfinityFlag workStart) = true ∧
          setupState (pointAddGenericFlag workStart) = false ∧
          setupState (pointAddDoubleFlag workStart) = false ∧
          Clean (pointAddBranchWork workStart) setupState
        at hsetup

      rcases hsetup with
        ⟨hinfinity, hgeneric, hdouble, hbranchClean⟩

      have hbranches :=
        pointAddBranches_infinity_correct
          workStart hC setupState
          hinfinity hgeneric hdouble hbranchClean

      simpa only [affineAdd_zero_left] using hbranches

  | some hR =>
      rename_i xR yR

      have hsetup :=
        pointAddSetup_some_correct
          pointReg outReg workStart
          (xC := xC) (yC := yC)
          hR st
          hpointLength hnodup hpoint hclean

      change
        regValue (pointAddX workStart) setupState = xR.val ∧
          regValue (pointAddY workStart) setupState = yR.val ∧
          setupState (pointAddInfinityFlag workStart) = false ∧
          setupState (pointAddGenericFlag workStart) =
            decide (xR ≠ xC) ∧
          setupState (pointAddDoubleFlag workStart) =
            decide (xR = xC ∧ yR ≠ -yC) ∧
          Clean (pointAddBranchWork workStart) setupState
        at hsetup

      rcases hsetup with
        ⟨hxReg, hyReg, hinfinity,
         hgeneric, hdouble, hbranchClean⟩

      by_cases hx : xR = xC

      · by_cases hinv : yR = -yC

        ·
          have hgeneric' :
              setupState
                (pointAddGenericFlag workStart) = false := by
            simpa [hx] using hgeneric

          have hdouble' :
              setupState
                (pointAddDoubleFlag workStart) = false := by
            simpa [hx, hinv] using hdouble

          have hbranches :=
            pointAddBranches_inverse_correct
              workStart hC setupState
              hinfinity hgeneric' hdouble' hbranchClean

          rw [affineAdd_inverse hR hC hx hinv]

          exact hbranches

        ·
          have hgeneric' :
              setupState
                (pointAddGenericFlag workStart) = false := by
            simpa [hx] using hgeneric

          have hdouble' :
              setupState
                (pointAddDoubleFlag workStart) = true := by
            simpa [hx, hinv] using hdouble

          have hbranches :=
            pointAddBranches_double_correct
              workStart hR hC hx hinv setupState
              hxReg hyReg
              hinfinity hgeneric' hdouble'
              hbranchClean

          have haff :
              affineAdd (.some hR) (.some hC) =
                doublePoint hR
                  (self_not_inverse_of_x_eq_of_not_inverse
                    hR hC hx hinv) := by
            unfold affineAdd
            simp [hx, hinv]

          rw [haff]

          exact hbranches

      ·
        have hgeneric' :
            setupState
              (pointAddGenericFlag workStart) = true := by
          simpa [hx] using hgeneric

        have hdouble' :
            setupState
              (pointAddDoubleFlag workStart) = false := by
          simpa [hx] using hdouble

        have hbranches :=
          pointAddBranches_generic_correct
            workStart hR hC hx setupState
            hxReg hyReg
            hinfinity hgeneric' hdouble'
            hbranchClean

        rw [affineAdd_generic hR hC hx]

        exact hbranches

/--
Structural facts needed to reverse `pointAddFiniteCompute`.

Unlike `pointAddFiniteCompute_correct`, this theorem contains no curve
arithmetic.  Its proof is obtained by composing the `HPFree`,
`wellFormed`, and `usesOnly` theorems for:

* `copyReg`,
* `loadConst`,
* `zeroFlag`,
* `equalFlag`,
* `fieldAdd`,
* `fieldSub`,
* `fieldMul`,
* `fieldInv`,
* `controlledCopyReg`.

The last conjunct records that `selected` really belongs to the declared
PointAdd workspace.
-/
theorem pointAddFiniteCompute_structural
    (pointReg outReg : List Wire)
    (workStart : Wire)
    {xC yC : Fp}
    (hC : curve.toAffine.Nonsingular xC yC)
    (hnodup :
      (pointReg ++ outReg ++ pointAddWork workStart).Nodup) :
    let compute :=
      pointAddFiniteCompute pointReg workStart hC
    Classical.HPFree compute ∧
      CircuitWellFormed compute ∧
      CircuitUsesOnly
        (pointReg ++ pointAddWork workStart)
        compute ∧
      (∀ w ∈ pointAddSelected workStart,
        w ∈ pointAddWork workStart) := by
  sorry

/--
Generic Bennett copy-out lemma.

Suppose `compute`

    |input⟩ |0_work⟩
        ↦
    |history⟩

and the register `src`, which lies inside `work`, contains `value` after
the forward computation.

If we do

    compute;
    copyReg src out;
    compute.reverse

then the forward history is erased while the copied value survives in
the disjoint public output register.

Hence the complete state is exactly

    writeReg out value st.

This theorem is completely independent of elliptic curves.
-/
theorem bennett_copyReg_eq_writeReg
    (compute : Circuit)
    (input src out work : List Wire)
    (st : BasisState)
    (value : Nat)
    (hfree : Classical.HPFree compute)
    (hwf : CircuitWellFormed compute)
    (huses :
      CircuitUsesOnly (input ++ work) compute)
    (hsrc :
      ∀ w ∈ src, w ∈ work)
    (hnodup :
      (input ++ out ++ work).Nodup)
    (hlen :
      out.length = src.length)
    (hclean :
      Clean out st)
    (hvalue :
      regValue src (Classical.run compute st) = value)
    (hbound :
      value < 2 ^ out.length) :
    Classical.run
        (circuit! {
          compute;
          Arithmetic.copyReg src out;
          compute.reverse
        })
        st =
      writeReg out value st := by
  sorry

/-! -------------------------------------------------------------------------
    Final PointAdd correctness
------------------------------------------------------------------------- -/

theorem pointAdd_correct
    [Fact (Nat.Prime p)]
    (pointReg outReg : List Wire)
    (workStart : Wire)
    (C R : Point)
    (st : BasisState)
    (hpointLength :
      pointReg.length = pointWidth)
    (houtLength :
      outReg.length = pointWidth)
    (hnodup :
      (pointReg ++ outReg ++ pointAddWork workStart).Nodup)
    (hpoint :
      regValue pointReg st = encodeNat R)
    (hclean :
      Clean (outReg ++ pointAddWork workStart) st) :
    Classical.run
        (pointAdd pointReg outReg workStart C)
        st =
      writeReg
        outReg
        (encode (R + C)).val
        st := by
  cases C with
  | zero =>
      have hlen : outReg.length = pointReg.length := by
        calc
          outReg.length = pointWidth := houtLength
          _ = pointReg.length := hpointLength.symm

      have hcleanOut : Clean outReg st :=
        Arithmetic.Clean.mono hclean (by
          intro w hw
          exact List.mem_append_left _ hw)

      have hbound : encodeNat R < 2 ^ outReg.length := by
        rw [houtLength]
        exact encodeNat_lt R

      have hcopy :=
        copyReg_eq_writeReg_of_value
          pointReg
          outReg
          (pointAddWork workStart)
          st
          (encodeNat R)
          hlen
          hnodup
          hcleanOut
          hpoint
          hbound

      change
        Classical.run (Arithmetic.copyReg pointReg outReg) st =
          writeReg outReg (encode (R + 0)).val st
      have henc : (encode (R + 0)).val = encodeNat R := by
        rw [add_zero, encode_val]
      rw [henc]
      exact hcopy

  | some hC =>
      rename_i xC yC

      let compute :=
        pointAddFiniteCompute pointReg workStart hC

      have hcleanWork :
          Clean (pointAddWork workStart) st :=
        Arithmetic.Clean.mono hclean (by
          intro w hw
          exact List.mem_append_right outReg hw)

      have hcleanOut : Clean outReg st :=
        Arithmetic.Clean.mono hclean (by
          intro w hw
          exact List.mem_append_left _ hw)

      have hforward :
          regValue
              (pointAddSelected workStart)
              (Classical.run compute st) =
            encodeNat (affineAdd R (.some hC)) := by
        simpa [compute] using
          pointAddFiniteCompute_correct
            pointReg
            outReg
            workStart
            hC
            R
            st
            hpointLength
            hnodup
            hpoint
            hcleanWork

      obtain ⟨hfree, hwf, huses, hselected⟩ :=
        pointAddFiniteCompute_structural
          pointReg
          outReg
          workStart
          hC
          hnodup

      have hlen :
          outReg.length =
            (pointAddSelected workStart).length := by
        simp [pointAddSelected, houtLength, pointWidth]

      have hbound :
          encodeNat (affineAdd R (.some hC)) <
            2 ^ outReg.length := by
        rw [houtLength]
        exact encodeNat_lt (affineAdd R (.some hC))

      have hbennett :=
        bennett_copyReg_eq_writeReg
          compute
          pointReg
          (pointAddSelected workStart)
          outReg
          (pointAddWork workStart)
          st
          (encodeNat (affineAdd R (.some hC)))
          hfree
          hwf
          huses
          hselected
          hnodup
          hlen
          hcleanOut
          hforward
          hbound

      rw [affineAdd_correct] at hbennett
      change
        Classical.run
            (circuit! {
              compute;
              Arithmetic.copyReg
                (pointAddSelected workStart)
                outReg;
              compute.reverse
            })
            st =
          writeReg outReg (encode (R + .some hC)).val st
      have henc :
          (encode (R + .some hC)).val =
            encodeNat (R + .some hC) := by
        rw [encode_val]
      rw [henc]
      simpa only [compute] using hbennett

end Secp256k1
end ShorECDLP
