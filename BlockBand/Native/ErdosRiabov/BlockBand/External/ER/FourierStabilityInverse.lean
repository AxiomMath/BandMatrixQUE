module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.DiscreteFourierGreen

/-!
# Fourier stability inverse for the cyclic profile

The namespace `ERFourierInverse` for the Fourier inverse of the stability operator of the cyclic
block profile; this module declares only a local `NeZero` instance and no results.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace ERNative.BlockBand
namespace GaussianRing
namespace ERFourierInverse

open scoped BigOperators
open ERProfile ERProfileAnalytic ERDiscreteFourier

local instance (p : Params) : NeZero p.n := p.nNeZero

end ERFourierInverse
end GaussianRing
end ERNative.BlockBand
