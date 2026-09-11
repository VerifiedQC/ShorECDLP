import ShorECDLP.Submission.«2607_13816».Arithmetic.UnitaryPrimitiveCounts
import ShorECDLP.Submission.«2607_13816».EEA.StepControl
namespace ShorECDLP.Paper2607_13816
open Quantum
/-- Exact primitive vector for the 259-bit work/9-bit shift-length production circuit. -/
theorem preShiftUnitary259_primitive (r : ShiftRegisters) (hl : ShiftLayout r)
    (hw : r.work.length=259) (hs : r.lengthS.length=9) :
    primitiveResources (.unitary (preShiftUnitary r) .done)=
      (⟨68,0,1067,566,0,0⟩ : PrimitiveResources) := by
  rw [primitiveResources_unitary_HPFree _ _ (preShiftUnitary_HPFree r),
    preShiftUnitary_xCount r hl,preShiftUnitary_cnotCount r hl (by omega),
    preShiftUnitary_toffoliCount r hl,rightTwoSwapCount_of_odd r.work (by omega) (by omega),hw,hs]
  rfl
/-- Exact primitive vector for the 259-bit work/9-bit shift-length production circuit. -/
theorem postShiftUnitary259_primitive (r : ShiftRegisters) (hl : ShiftLayout r)
    (hw : r.work.length=259) (hs : r.lengthS.length=9) :
    primitiveResources (.unitary (postShiftUnitary r) .done)=
      (⟨64,0,1065,566,0,0⟩ : PrimitiveResources) := by
  rw [primitiveResources_unitary_HPFree _ _ (postShiftUnitary_HPFree r),
    postShiftUnitary_xCount r hl,postShiftUnitary_cnotCount r hl (by omega),
    postShiftUnitary_toffoliCount r hl,rightTwoSwapCount_of_odd r.work (by omega) (by omega),hw,hs]
  rfl
/-- The explicit source inverse has its own X cost; no adjoint cost is substituted. -/
theorem terminalPaddingForward259_primitive (r : TerminalPaddingRegisters)
    (hl : TerminalPaddingLayout r) (hw : r.work2.length=259) (hs : r.lengthS.length=9) :
    primitiveResources (.unitary (terminalPaddingForward r) .done)=
      (⟨36,0,527,305,0,0⟩ : PrimitiveResources) := by
  rw [primitiveResources_unitary_HPFree _ _ (terminalPaddingForward_HPFree r),
    terminalPaddingForward_xCount r hl,terminalPaddingForward_cnotCount r hl,
    terminalPaddingForward_toffoliCount r hl,hw,hs]
  rfl
/-- The explicit source inverse has its own X cost; no adjoint cost is substituted. -/
theorem terminalPaddingInverse259_primitive (r : TerminalPaddingRegisters)
    (hl : TerminalPaddingLayout r) (hw : r.work2.length=259) (hs : r.lengthS.length=9) :
    primitiveResources (.unitary (terminalPaddingInverse r) .done)=
      (⟨68,0,527,305,0,0⟩ : PrimitiveResources) := by
  rw [primitiveResources_unitary_HPFree _ _ (terminalPaddingInverse_HPFree r),
    terminalPaddingInverse_xCount r hl,terminalPaddingInverse_cnotCount r hl,
    terminalPaddingInverse_toffoliCount r hl,hw,hs]
  rfl
end ShorECDLP.Paper2607_13816
