module

public import BlockBand.Native.PSSS.BlockBand.Basic.Indices
public import BlockBand.Native.PSSS.BlockBand.Spectral.Ordered
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Gaussian normalization conventions

The normalizing constant of the GUE density with diagonal variance `t` and total off-diagonal
complex variance `t`: diagonal entries are real Gaussians of variance `t`, off-diagonal entries
are circular complex Gaussians with `E|z|² = t`. The matrix-valued density itself is not
constructed here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace PSSSNative.BlockBand

/-- Normalizing constant `(2πt)^{d/2} (πt)^{d(d-1)/2}` of the GUE density with diagonal variance
`t` and total off-diagonal complex variance `t`. -/
def gueNormalizer (d : ℕ) (t : ℝ) : ℝ :=
  (2 * Real.pi * t) ^ ((d : ℝ) / 2) *
    (Real.pi * t) ^ (((d : ℝ) * ((d : ℝ) - 1)) / 2)

end PSSSNative.BlockBand
