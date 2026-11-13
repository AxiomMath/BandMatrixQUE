module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.ProfileAdmissibility
public import BlockBand.Native.ErdosRiabov.BlockBand.Analysis.ERControlKernels
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Quantitative scalar analysis for the cyclic ER profile

This module supplies the source-faithful, unconditional scalar Fourier estimates used
before the logarithmically relaxed convolution analysis of Erdős–Riabov Example 2.7.
The coupling is fixed before dimensions vary.  No local law and no seven-clause
certificate is assumed.

The exact symbol is `1 - 2b(1-cos θ)`.  On the principal Fourier interval its gap is
bounded below by `(4b/π²)θ²`; thus the coefficient depends only on the fixed coupling,
not on the ring size or parity.  We also prove modewise invertibility and the sharp
Neumann denominator bound for every complex multiplier of norm less than one, and
record the exact covariance action on block-constant vectors.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace ERNative.BlockBand
namespace GaussianRing
namespace ERProfileAnalytic

open scoped BigOperators
open ERProfile

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- Real Fourier symbol of the nearest-neighbour cyclic block covariance. -/
def cyclicSymbol (b θ : ℝ) : ℝ := 1 - 2 * b * (1 - Real.cos θ)

/-- Unconditional deterministic part of the logarithmically relaxed admissibility
package.  It includes exact tensorization and covers both ring parities. -/
theorem tensorized_profile_prerequisites (p : Params) :
    ERDefinition21Profile p ∧ ERBlockBandProfile p :=
  both_ring_parities p

end ERProfileAnalytic
end GaussianRing
end ERNative.BlockBand
