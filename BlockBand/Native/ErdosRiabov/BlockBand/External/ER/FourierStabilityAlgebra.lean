module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.FourierStabilityInverse

/-!
# Fourier stability inverse: the cyclic symbol in the cosine coordinate

Defines the Fourier symbol `1 - 2b(1 - u)` of the cyclic block profile as a function of the
cosine coordinate `u = cos θ`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace ERNative.BlockBand
namespace GaussianRing
namespace ERFourierAlgebra

open ERProfile ERProfileAnalytic ERDiscreteFourier ERFourierInverse

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- The cyclic symbol as a function of the cosine coordinate. -/
def cyclicSymbolCos (b u : ℝ) : ℝ := 1 - 2 * b * (1 - u)

end ERFourierAlgebra
end GaussianRing
end ERNative.BlockBand
