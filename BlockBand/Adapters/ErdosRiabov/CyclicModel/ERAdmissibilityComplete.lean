module

public import BlockBand.Adapters.ErdosRiabov.CyclicModel.ERControlKernels
public import Mathlib

/-!
# The explicit cyclic control family for Erdős–Riabov admissibility

The exponential control `(ℓ η)⁻¹ exp (-a d / ℓ)`, with the localization length
`ℓ = min (W / √η) N` and the flattened cyclic site distance `d`, as a control family on
the Gaussian ring (compare Erdős–Riabov Definitions 2.4–2.5 and Example 2.7).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Adapters.ErdosRiabov.CyclicModel
namespace GaussianRing

open scoped BigOperators

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- The exponential control `(ℓ η)⁻¹ exp (-a d / ℓ)`. The decay constant `a` is fixed
before `η`, the sites, and the ring dimensions. -/

-- The floor exponent `D` is an unused argument.
def erManuscriptCyclicControl (p : Params) (a _D : ℝ) : ERControlFamily p :=
  fun η x y =>
    let ell := erLocalizationLength p η
    (1 / (ell * η)) *
      Real.exp (-a * (erSiteDistance p x y : ℝ) / ell)

end GaussianRing
end BlockBand.Adapters.ErdosRiabov.CyclicModel
