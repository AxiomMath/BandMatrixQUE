module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.FourierStabilityAlgebra

/-!
# Exact Fourier Green-kernel convolution

This module reconstructs the Fourier-defined scalar stability inverse as convolution
with the explicitly normalized cyclic Green kernel.  It is an exact finite identity;
no decay estimate or analytic certificate is assumed.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace ERNative.BlockBand
namespace GaussianRing
namespace ERGreenConvolution

open scoped BigOperators
open ERProfile ERDiscreteFourier ERFourierInverse ERFourierAlgebra

local instance (p : Params) : NeZero p.n := p.nNeZero

end ERGreenConvolution
end GaussianRing
end ERNative.BlockBand
