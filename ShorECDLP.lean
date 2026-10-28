import ShorECDLP.Submission.«2607_13816».Challenge.ExceptionalFields
import ShorECDLP.Submission.«2607_13816».Challenge.EndpointTransposition
import ShorECDLP.Submission.«2607_13816».Challenge.FixedMatching
import ShorECDLP.Submission.«2607_13816».Challenge.RegisterEquality
import ShorECDLP.Submission.«2607_13816».Challenge.EndpointSwap
import ShorECDLP.Submission.«2607_13816».Challenge.SharedTable
import ShorECDLP.Submission.«2607_13816».Challenge.Coordinate
import ShorECDLP.Submission.«2607_13816».Challenge.RetainedRecords
import ShorECDLP.Submission.«2607_13816».Challenge.InPlace
import ShorECDLP.Submission.«2607_13816».Challenge.ZeroLeaf
import ShorECDLP.Submission.«2607_13816».Challenge.RangeScan
import ShorECDLP.Submission.«2607_13816».Challenge.ZeroMap
import ShorECDLP.Submission.«2607_13816».Challenge.LengthRefresh
import ShorECDLP.Submission.«2607_13816».Challenge.Endpoint
import ShorECDLP.Submission.«2607_13816».Challenge.MeasuredStep
import ShorECDLP.Submission.«2607_13816».Challenge.MeasuredSchedule
import ShorECDLP.Submission.«2607_13816».Challenge.MeasuredWrapper
import ShorECDLP.Submission.«2607_13816».Challenge.MeasuredWorkspace
import ShorECDLP.Submission.«2607_13816».Challenge.Relabel
import ShorECDLP.Submission.«2607_13816».Challenge.Wrapper
import ShorECDLP.Submission.«2607_13816».Challenge.Workspace
import ShorECDLP.Submission.«2607_13816».Challenge.Schedule
import ShorECDLP.Submission.«2607_13816».Challenge.IntervalWhole
import ShorECDLP.Submission.«2607_13816».Challenge.Coefficient
import ShorECDLP.Submission.«2607_13816».Challenge.EEACenter
import ShorECDLP.Submission.«2607_13816».Challenge.Unary
import ShorECDLP.Submission.«2607_13816».Challenge.VChain
import ShorECDLP.Submission.«2607_13816».Challenge.Square
import ShorECDLP.Submission.«2607_13816».Challenge.Horner
import ShorECDLP.Submission.«2607_13816».Challenge.SignedWindow
import ShorECDLP.Submission.«2607_13816».Challenge.ModularAdd
import ShorECDLP.Submission.«2607_13816».Challenge.GidneyAdd
import ShorECDLP.Submission.«2607_13816».Challenge.OddFields
import ShorECDLP.Submission.«2607_13816».Challenge.Lookup
import ShorECDLP.Submission.«2607_13816».Challenge.Coefficients
import ShorECDLP.Submission.«2607_13816».Challenge.PointTable
import ShorECDLP.Submission.«2607_13816».Challenge.Fourier
import ShorECDLP.Submission.«2607_13816».Challenge.Support
import ShorECDLP.Submission.«2607_13816».Challenge.Records
import ShorECDLP.Submission.«2607_13816».Challenge.Positions
import ShorECDLP.Submission.«2607_13816».Challenge.Gates
import ShorECDLP.Submission.«2607_13816».Challenge.Reset
-- ShorECDLP: shared verified semantics and independent Bitcoin ECDLP submissions.
--
-- This is the only Lean module that imports both submission trees. Import-direction
-- checks in `scripts/check-source.py` keep their implementations isolated.
import ShorECDLP.Framework.InstructionSet
import ShorECDLP.Framework.CostModel
import ShorECDLP.Framework.BasisState
import ShorECDLP.Framework.Classical.Semantics
import ShorECDLP.Framework.Quantum.Adaptive
import ShorECDLP.Framework.Quantum.CoherentRefinement
import ShorECDLP.Framework.Quantum.MeasurementUncompute
import ShorECDLP.Framework.Quantum.Measurement
import ShorECDLP.Framework.Repetition
import ShorECDLP.Math.All
import ShorECDLP.Submission.Naive.All
import ShorECDLP.Judge.Main
import ShorECDLP.Submission.Entrant.Main
import ShorECDLP.Submission.«2607_13816».All

import ShorECDLP.Challenge.Template
import ShorECDLP.Challenge.StraightLine
import ShorECDLP.Challenge.Contract
import ShorECDLP.Challenge.Smoke
import ShorECDLP.Challenge.StraightSmoke
import ShorECDLP.Challenge.DecoderSmoke

import ShorECDLP.Submission.Naive.Challenge.Readout
import ShorECDLP.Submission.Naive.Challenge.Probability
import ShorECDLP.Submission.Naive.Challenge.ResetRepeat
import ShorECDLP.Submission.Naive.Challenge.Physical

import ShorECDLP.Submission.Naive.Challenge.FixedReset
import ShorECDLP.Submission.Naive.Challenge.Constants
import ShorECDLP.Submission.Naive.Challenge.PointGates
import ShorECDLP.Submission.Naive.Challenge.TrialGates
import ShorECDLP.Submission.Naive.Challenge.Static
import ShorECDLP.Submission.Naive.Challenge.StaticResources
import ShorECDLP.Submission.Naive.Challenge.RepeatedEntry
import ShorECDLP.Submission.Naive.Challenge.RecordPositions
import ShorECDLP.Submission.Naive.Challenge.Certificate

import ShorECDLP.Submission.Naive.Challenge.NumericCosts
import ShorECDLP.Submission.Naive.Challenge.NumericQubits
import ShorECDLP.Submission.Naive.Challenge.NumericLengths
import ShorECDLP.Submission.Naive.Challenge.NumericCertificate
import ShorECDLP.Challenge.ExtendedContract
import ShorECDLP.Submission.Naive.Challenge.ExtendedCertificate

import ShorECDLP.Challenge.PointFields
import ShorECDLP.Submission.«2607_13816».Challenge.CertificateAssembly
import ShorECDLP.Submission.«2607_13816».Challenge.FixedNetwork
import ShorECDLP.Submission.«2607_13816».Challenge.EndpointLoad
import ShorECDLP.Submission.«2607_13816».Challenge.MatchingPhysical
import ShorECDLP.Submission.«2607_13816».Challenge.EndpointEncoding
import ShorECDLP.Submission.«2607_13816».Challenge.EndpointQROM
import ShorECDLP.Submission.«2607_13816».Challenge.EndpointSandwich
import ShorECDLP.Submission.«2607_13816».Challenge.EndpointCoherent
import ShorECDLP.Submission.«2607_13816».Challenge.Outer
import ShorECDLP.Submission.«2607_13816».Challenge.BatchedEndpoint
import ShorECDLP.Submission.«2607_13816».Challenge.BatchState
import ShorECDLP.Submission.«2607_13816».Challenge.BatchPlacement
import ShorECDLP.Submission.«2607_13816».Challenge.CursorShift
import ShorECDLP.Submission.«2607_13816».Challenge.WindowBody
import ShorECDLP.Submission.«2607_13816».Challenge.BatchQuery
import ShorECDLP.Submission.«2607_13816».Challenge.BatchExecution
import ShorECDLP.Submission.«2607_13816».Challenge.BatchCoherent
import ShorECDLP.Submission.«2607_13816».Challenge.BatchFrame
import ShorECDLP.Submission.«2607_13816».Challenge.BatchPhysical
import ShorECDLP.Submission.«2607_13816».Challenge.BatchCost
import ShorECDLP.Submission.«2607_13816».Challenge.PlacedBatch
import ShorECDLP.Submission.«2607_13816».Challenge.LookupPhysical
import ShorECDLP.Submission.«2607_13816».Challenge.BatchTemplate

import ShorECDLP.Submission.«2607_13816».Challenge.CoordinateConjugacy

import ShorECDLP.Submission.«2607_13816».Challenge.AccumulatorEncoding

import ShorECDLP.Submission.«2607_13816».Challenge.WindowNegation
import ShorECDLP.Submission.«2607_13816».Challenge.OuterResources
import ShorECDLP.Submission.«2607_13816».Challenge.BatchBoundary
import ShorECDLP.Submission.«2607_13816».Challenge.BatchedWindowState
import ShorECDLP.Submission.«2607_13816».Challenge.BatchedWindowCoherent
import ShorECDLP.Submission.«2607_13816».Challenge.PreparedBatch

import ShorECDLP.Submission.«2607_13816».Challenge.MeasurementBridge
import ShorECDLP.Submission.«2607_13816».Challenge.WindowCounts
import ShorECDLP.Submission.«2607_13816».Challenge.WindowBudget
import ShorECDLP.Submission.«2607_13816».Challenge.LookupSlots
import ShorECDLP.Submission.«2607_13816».Challenge.ArithmeticSlots
import ShorECDLP.Submission.«2607_13816».Challenge.DecoderSlots
import ShorECDLP.Submission.«2607_13816».Challenge.EEACellSlots
import ShorECDLP.Submission.«2607_13816».Challenge.EEALengthSlots
import ShorECDLP.Submission.«2607_13816».Challenge.EEAScheduleSlots
import ShorECDLP.Submission.«2607_13816».Challenge.StructuralSupport

import ShorECDLP.Submission.«2607_13816».Challenge.BatchSupport
import ShorECDLP.Submission.«2607_13816».Challenge.ArithmeticSupport
import ShorECDLP.Submission.«2607_13816».Challenge.ControlSupport
import ShorECDLP.Submission.«2607_13816».Challenge.WindowSupport

import ShorECDLP.Submission.«2607_13816».Challenge.MultiplicationSupport
import ShorECDLP.Submission.«2607_13816».Challenge.EEACenterSupport
import ShorECDLP.Submission.«2607_13816».Challenge.EEACoreSupport
import ShorECDLP.Submission.«2607_13816».Challenge.PhaseSupport
import ShorECDLP.Submission.«2607_13816».Challenge.CoefficientSupport
import ShorECDLP.Submission.«2607_13816».Challenge.IntervalSupport
import ShorECDLP.Submission.«2607_13816».Challenge.StepSupport
import ShorECDLP.Submission.«2607_13816».Challenge.LengthSupport
import ShorECDLP.Submission.«2607_13816».Challenge.EndpointSupport
import ShorECDLP.Submission.«2607_13816».Challenge.WrapperSupport
import ShorECDLP.Submission.«2607_13816».Challenge.InPlaceSupport
import ShorECDLP.Submission.«2607_13816».Challenge.CoordinateSupport
import ShorECDLP.Submission.«2607_13816».Challenge.CompleteSupport
import ShorECDLP.Submission.«2607_13816».Challenge.ProductionEEASlots
import ShorECDLP.Submission.«2607_13816».Challenge.InPlaceSlots
import ShorECDLP.Submission.«2607_13816».Challenge.WindowSlots
import ShorECDLP.Submission.«2607_13816».Challenge.ActualWindow
import ShorECDLP.Submission.«2607_13816».Challenge.WindowPhysical
import ShorECDLP.Submission.«2607_13816».Challenge.ModularPhysical

import ShorECDLP.Submission.«2607_13816».Challenge.SquarePhysical
import ShorECDLP.Submission.«2607_13816».Challenge.InPlacePhysical
import ShorECDLP.Submission.«2607_13816».Challenge.EEACenterPhysical
import ShorECDLP.Submission.«2607_13816».Challenge.EEAStructuralPhysical

import ShorECDLP.Submission.«2607_13816».Challenge.EEAIntervalPhysical

import ShorECDLP.Submission.«2607_13816».Challenge.MeasuredEEAPhysical

import ShorECDLP.Submission.«2607_13816».Challenge.InPlaceCompletePhysical

import ShorECDLP.Submission.«2607_13816».Challenge.CoordinatePhysical

import ShorECDLP.Submission.«2607_13816».Challenge.ActualPhysical
import ShorECDLP.Submission.«2607_13816».Challenge.UniformT
import ShorECDLP.Submission.«2607_13816».Challenge.ResourceCertificate
