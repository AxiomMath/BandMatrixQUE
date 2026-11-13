module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.CyclicResolventDecay

/-!
# Quantitative normalization of the cyclic resolvent jump

The source jump of the nearest-neighbour recurrence is the square root, up to
sign, of its characteristic discriminant.  Factoring that discriminant gives
a lower bound at the square-root radial-margin scale with a constant depending
only on the fixed bond weight.  Combining it with the contracting-root gap
removes the final unspecified denominator from the cyclic Green estimate.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace ERNative.BlockBand.GaussianRing.ERJumpNormalization

open ERDiscreteFourier ERFourierInverse ERFourierAlgebra ERCharacterAngle
  ERNearestNeighbor ERCyclicDecay ERHerglotz

local instance (p : Params) : NeZero p.n := p.nNeZero

end ERNative.BlockBand.GaussianRing.ERJumpNormalization
