import ShorECDLP.Submission.«2607_13816».Challenge.ActualPair
namespace ShorECDLP.Paper2607_13816.ChallengeMigration
open Quantum ShorECDLP.Challenge Secp256k1
-- Chronological emitted bits: the first measurement has weight 1.
example : readWord (true :: List.replicate 15 false) (List.range 16) = some 1 := by decide +kernel
example : fourierWordLSB (true :: List.replicate 15 false) = 1 := by decide +kernel
-- The last measurement has weight 2^15, not weight 1.
example : readWord (List.replicate 15 false ++ [true]) (List.range 16) = some 32768 := by decide +kernel
example : fourierWordLSB (List.replicate 15 false ++ [true]) = 32768 := by decide +kernel
-- The physical Fourier branch uses precisely that integer in its kernel exponent.
example (s : BasisState) :
    fourierBranch .inverse streamAddress.reverse List.nil (true :: List.replicate 15 false) (ket s) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)^16) *
        dyadicFourierKernel .inverse 16 (fourierWordMSB (streamAddress.reverse.map s)) 1) •
        ket (fourierClear streamAddress.reverse s) := by
  simpa only [show streamAddress.reverse.length = 16 by decide +kernel,
    show fourierWordLSB (true :: List.replicate 15 false) = 1 by decide +kernel] using
    fourierBranch_ket_kernel .inverse streamAddress.reverse (by decide +kernel)
      (true :: List.replicate 15 false) (by decide +kernel) s
example (s : BasisState) :
    fourierBranch .inverse streamAddress.reverse List.nil (List.replicate 15 false ++ [true]) (ket s) =
      (((((Real.sqrt 2)⁻¹ : ℝ) : ℂ)^16) *
        dyadicFourierKernel .inverse 16 (fourierWordMSB (streamAddress.reverse.map s)) 32768) •
        ket (fourierClear streamAddress.reverse s) := by
  simpa only [show streamAddress.reverse.length = 16 by decide +kernel,
    show fourierWordLSB (List.replicate 15 false ++ [true]) = 32768 by decide +kernel] using
    fourierBranch_ket_kernel .inverse streamAddress.reverse (by decide +kernel)
      (List.replicate 15 false ++ [true]) (by decide +kernel) s
end ShorECDLP.Paper2607_13816.ChallengeMigration
