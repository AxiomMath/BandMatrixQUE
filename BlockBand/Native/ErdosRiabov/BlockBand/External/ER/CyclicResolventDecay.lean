module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.NearestNeighborResolvent

/-!
# Finite cyclic resolvent decay

The two oriented paths on a cycle produce the numerator
`ρ^d + ρ^(n-d)`.  This module records its exact wraparound denominator,
the jump normalization for the nearest-neighbour recurrence, and
dimension/parity-uniform norm estimates.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace ERNative.BlockBand.GaussianRing.ERCyclicDecay

open ERDiscreteFourier ERFourierInverse ERFourierAlgebra
  ERCharacterAngle ERNearestNeighbor

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- Sum of the two finite cyclic paths with displacement `d`. -/
def cyclicTwoPathNumerator (p : Params) (ρ : ℂ) (d : ℕ) : ℂ :=
  ρ ^ d + ρ ^ (p.n - d)

end ERNative.BlockBand.GaussianRing.ERCyclicDecay
