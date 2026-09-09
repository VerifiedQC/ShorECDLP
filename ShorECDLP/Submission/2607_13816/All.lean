import ShorECDLP.Submission.«2607_13816».EEA.EndIterationArithmetic
import ShorECDLP.Submission.«2607_13816».EEA.LengthArithmetic
import ShorECDLP.Submission.«2607_13816».EEA.ActiveTrace
import ShorECDLP.Submission.«2607_13816».EEA.TerminalTrace
import ShorECDLP.Submission.«2607_13816».EEA.RouteBounds
import ShorECDLP.Submission.«2607_13816».EEA.InitialPacked
import ShorECDLP.Submission.«2607_13816».EEA.FirstStep
import ShorECDLP.Submission.«2607_13816».EEA.InitialEncoding
import ShorECDLP.Submission.«2607_13816».EEA.PreprocessResources
import ShorECDLP.Submission.«2607_13816».EEA.Preprocess
import ShorECDLP.Submission.«2607_13816».EEA.WorkPreparation
import ShorECDLP.Submission.«2607_13816».EEA.LengthInitialize
import ShorECDLP.Submission.«2607_13816».EEA.Centering
import ShorECDLP.Submission.«2607_13816».Arithmetic.ConstMinus
import ShorECDLP.Submission.«2607_13816».Arithmetic.HornerInverse
import ShorECDLP.Submission.«2607_13816».Arithmetic.Halving
import ShorECDLP.Submission.«2607_13816».Arithmetic.ModularSub
import ShorECDLP.Submission.«2607_13816».Arithmetic.ResourceGrowth
import ShorECDLP.Submission.«2607_13816».Arithmetic.Square
import ShorECDLP.Submission.«2607_13816».Arithmetic.HornerMul
import ShorECDLP.Submission.«2607_13816».Arithmetic.Doubling
import ShorECDLP.Submission.«2607_13816».Arithmetic.ModularAdd
import ShorECDLP.Submission.«2607_13816».Arithmetic.UncontrolledCompare
import ShorECDLP.Submission.«2607_13816».Arithmetic.ModularCorrection
import ShorECDLP.Submission.«2607_13816».Arithmetic.GidneyCompare
import ShorECDLP.Submission.«2607_13816».Arithmetic.GidneyAdd
import ShorECDLP.Submission.«2607_13816».Arithmetic.ConstCarry
import ShorECDLP.Submission.«2607_13816».Arithmetic.Compare
import ShorECDLP.Submission.«2607_13816».Arithmetic.CarryAdd
import ShorECDLP.Submission.«2607_13816».Canary.AdaptiveCPhase
import ShorECDLP.Submission.«2607_13816».EEA.BitCircuits
import ShorECDLP.Submission.«2607_13816».EEA.Increment
import ShorECDLP.Submission.«2607_13816».EEA.MeasuredAnd
import ShorECDLP.Submission.«2607_13816».EEA.UnaryIteration
import ShorECDLP.Submission.«2607_13816».EEA.UnaryAction
import ShorECDLP.Submission.«2607_13816».EEA.DualUnaryAction
import ShorECDLP.Submission.«2607_13816».EEA.TreeBuilder
import ShorECDLP.Submission.«2607_13816».EEA.Ripple
import ShorECDLP.Submission.«2607_13816».EEA.IntervalLeaf
import ShorECDLP.Submission.«2607_13816».EEA.IntervalCleanup
import ShorECDLP.Submission.«2607_13816».EEA.LengthUpdate
import ShorECDLP.Submission.«2607_13816».EEA.Affine
import ShorECDLP.Submission.«2607_13816».EEA.WordNat
import ShorECDLP.Submission.«2607_13816».EEA.Endpoint
import ShorECDLP.Submission.«2607_13816».EEA.ZeroMap
import ShorECDLP.Submission.«2607_13816».EEA.LengthBlocks
import ShorECDLP.Submission.«2607_13816».EEA.Interval
import ShorECDLP.Submission.«2607_13816».EEA.PhaseUpdate
import ShorECDLP.Submission.«2607_13816».EEA.Shift
import ShorECDLP.Submission.«2607_13816».EEA.QuotientSwap
import ShorECDLP.Submission.«2607_13816».EEA.CoefficientPrefix
import ShorECDLP.Submission.«2607_13816».EEA.TBoundary
import ShorECDLP.Submission.«2607_13816».EEA.CoefficientPrefixInverse
import ShorECDLP.Submission.«2607_13816».EEA.StepControl
import ShorECDLP.Submission.«2607_13816».EEA.EndIteration
import ShorECDLP.Submission.«2607_13816».EEA.IndexedStep
import ShorECDLP.Submission.«2607_13816».EEA.Schedule
import ShorECDLP.Submission.«2607_13816».EEA.ScheduleLayout
import ShorECDLP.Submission.«2607_13816».EEA.Windows

import ShorECDLP.Submission.«2607_13816».EEA.ShiftCounter

/-!
# arXiv:2607.13816v2 submission

Root-closure sentinel for the independent space-efficient submission. Declarations live
under the namespace `ShorECDLP.Paper2607_13816`.
-/
