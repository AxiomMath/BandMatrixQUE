module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.CharacterAngle

/-!
# ER stability consequences

The unique sign-dependent Herglotz transform, the spectral domain and the Θ/Ξ
matrices are defined in the core ER API.  This module contains only analytic
consequences for the core Θ scalar multiplier; it defines no copy of those objects.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace ERNative.BlockBand.GaussianRing.ERHerglotz

open ERDiscreteFourier ERFourierInverse ERFourierAlgebra ERCharacterAngle

local instance (p : Params) : NeZero p.n := p.nNeZero

end ERNative.BlockBand.GaussianRing.ERHerglotz
