module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.CovarianceTensorizationAssembly
public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.Clause1CyclicControl
public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.ScalarProfileControl
public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.LocalLawBootstrap

/-!
# Exact dependency assembly for the ER local-law bootstrap

This module contains no declarations. Through its imports it collects the Gaussian-ring
covariance calculation and the scalar control estimates used by the Erdős–Riabov
bootstrap.

The site covariance is normalized by `S_{xy} = C_{kl}/W`, has row mass exactly one,
and is used below with the constant weight `1`.  The scalar control has localization
length `min (W / sqrt η) L`, exponential coefficient `1`, floor exponent `8`, and
comparison constant `6 * exp 1`.  Clause (i) instead retains its sharp bond-dependent
decay `clause1Decay b` and comparison constant `clause1ComparisonConstant b`.
All statements quantify over every finite `Params`, hence cover even and odd ring
lengths with no parity-dependent constant.

This is not an ER local law: the nearby-scale part of clause (iv), clauses (v)--(vii), the
probabilistic fluctuation estimates, continuity input, and finite stochastic bootstrap
are not treated here, and no hypothesis asserting a local law is used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace ERNative.BlockBand
namespace GaussianRing
namespace ERLocalLawBootstrapAssembly

open scoped BigOperators
open ERProfile ERExactGaussianMoments ERCovarianceTensorizationAssembly
open ERScalarProfileControl ERClause1

local instance (p : Params) : NeZero p.n := p.nNeZero

end ERLocalLawBootstrapAssembly
end GaussianRing
end ERNative.BlockBand
