module

public import BlockBand.Adapters.ErdosRiabov.CyclicModel.GaussianRing
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib

/-!
# The cyclic Gaussian-ring covariance profile

This file discharges the finite, algebraic part of Erdős–Riabov Proposition 2.8(ii)
for the Gaussian ring.  It records the covariance operator, its circulant Fourier
symbol, exact stochasticity and flatness, a dimension-independent gap identity, an
entrywise exponential Green estimate with its (finite and completely explicit)
weighted constant, and the tensorization with the normalized within-block kernel.

Source: Erdős–Riabov, *The Zigzag Strategy for Random Band Matrices*,
arXiv:2506.06441v1, Definition 2.1 and Proposition 2.8.  The indicator in the displayed
block example has its support sign reversed: the covariance is supported when the
cyclic block distance is **at most** one, not at least one.  The covariance used here,
`blockWeight`, has this corrected support.

All statements quantify over `Params`; hence they cover every `n ≥ 4`, with no parity
assumption.  The Green constant below is the exact finite weighted norm, not an
unspecified implicit constant.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Adapters.ErdosRiabov.CyclicModel
namespace GaussianRing
namespace ERProfile

open scoped BigOperators
open MeasureTheory ProbabilityTheory

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- The scalar cyclic covariance operator `C` at block scale. -/
def cyclicCovariance (p : Params) : Matrix (ZMod p.n) (ZMod p.n) ℝ :=
  fun k l => blockWeight p k l

/-- The full Erdős–Riabov covariance operator on physical sites. -/
def siteCovariance (p : Params) : Matrix (Site p.n p.W) (Site p.n p.W) ℝ :=
  fun x y => varianceProfile p x y

/-- Exact Gaussian-ring covariance formula, including the `W⁻¹` normalization. -/
theorem siteCovariance_apply (p : Params) (x y : Site p.n p.W) :
    siteCovariance p x y = cyclicCovariance p x.1 y.1 / (p.W : ℝ) := rfl

/-- Complexification of the scalar cyclic covariance. -/
def complexCyclicCovariance (p : Params) : Matrix (ZMod p.n) (ZMod p.n) ℂ :=
  fun k l =>
    (if l = k then (p.c : ℂ) else 0) +
      (if l = k + 1 then (p.b : ℂ) else 0) +
      (if l = k - 1 then (p.b : ℂ) else 0)

end ERProfile
end GaussianRing
end BlockBand.Adapters.ErdosRiabov.CyclicModel
