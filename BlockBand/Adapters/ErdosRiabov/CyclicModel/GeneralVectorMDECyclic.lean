module

public import BlockBand.Adapters.ErdosRiabov.CyclicModel.GeneralVectorMDE
public import BlockBand.Adapters.ErdosRiabov.CyclicModel.CyclicResolventDecay
public import BlockBand.Adapters.ErdosRiabov.CyclicModel.ProfileAdmissibility
public import Mathlib

/-!
# The general vector MDE package on the cyclic Gaussian-ring profile

This module instantiates `ERGeneralVectorMDE` for the fixed cyclic site profile
`varianceProfile p = siteCovariance p`, using the cyclic block distance
`cyclicBlockDistance p x.1 y.1` on physical sites.  It proves the cyclic triangle
inequality and the exact support radius one of the profile, which give the
exponential off-diagonal decay of the ER kernels `erTheta` and `erXi`.

Source: Erdős–Riabov, *The Zigzag Strategy for Random Band Matrices*,
arXiv:2506.06441v1, ER (2.10) for `Θ`, `Ξ`.
Normalization: `S_xy = blockWeight / W`, row sums exactly `1`; resolvent sign
`G(z) = (z - H)⁻¹`; `m = erSemicircleStieltjes`.  Every bound is uniform in
`p` (every `n ≥ 4`, both parities, every `W ≥ 1`) and in the spectral parameters
beyond the displayed dependence; no limit is taken.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Adapters.ErdosRiabov.CyclicModel
namespace GaussianRing
namespace ERGeneralVectorMDECyclic

open scoped BigOperators
open ERGeneralVectorMDE ERCyclicDecay

local instance (p : Params) : NeZero p.n := p.nNeZero

/-!
## Cyclic block distance
-/

@[simp] theorem cyclicBlockDistance_self (p : Params) (x : ZMod p.n) :
    cyclicBlockDistance p x x = 0 := by
  simp [cyclicBlockDistance, orientedBlockDistance]

end ERGeneralVectorMDECyclic
end GaussianRing
end BlockBand.Adapters.ErdosRiabov.CyclicModel
