module

public import BlockBand.Adapters.ErdosRiabov.CyclicModel.Clause1CyclicControl
public import Mathlib

/-!
# Source-faithful normalization of the scalar ER profile

The fixed-bond proof of clause (i) has decay
`min (1 / 2) (1 - 2b)`, not decay one.  This file puts the elementary
parts of the scalar admissibility calculation in that same normalization.
In particular it does not identify the two controls, and it does not assert
any bound uniform as `b ↑ 1 / 2`.

Source: Erdős–Riabov, Proposition 2.8(i), equation (2.18), and Definition
2.4(ii)--(iv), with the corrected nearest-neighbour support convention.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Adapters.ErdosRiabov.CyclicModel
namespace GaussianRing
namespace ERScalarProfileSourceFaithfulNormalization

open scoped BigOperators
open ERScalarProfileControl ERClause1 ERCyclicDecay ERCyclicSummation

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- The bond-dependent decay which is proved by the Fourier argument. -/
def sourceFaithfulDecay (p : Params) : ℝ := clause1Decay p.b

theorem sourceFaithfulDecay_pos (p : Params) : 0 < sourceFaithfulDecay p :=
  clause1Decay_pos p.b_pos p.b_lt_half

end ERScalarProfileSourceFaithfulNormalization
end GaussianRing
end BlockBand.Adapters.ErdosRiabov.CyclicModel
