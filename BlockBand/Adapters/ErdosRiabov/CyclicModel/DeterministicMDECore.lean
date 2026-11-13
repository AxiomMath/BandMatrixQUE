module

public import BlockBand.Adapters.ErdosRiabov.CyclicModel.CyclicGreenSummation
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Basic.Complex.Basic
public import Mathlib

/-!
# Deterministic MDE core on the ER spectral domain

This module packages the deterministic pieces of the external vector-MDE lemma that are
already consequences of the sign-dependent semicircle branch and
the explicit cyclic Fourier inverse.  It does not assert the full vector-MDE
statement and does not package any of the seven control-family clauses.

In particular, the lower half-plane is handled only through
`erSemicircleStieltjes`, never by evaluating `erSemicircleStieltjesUpperFormula` there
(that formula is the upper half-plane formula and is false in the lower half-plane).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Adapters.ErdosRiabov.CyclicModel
namespace GaussianRing
namespace ERDeterministicMDECore

open scoped BigOperators
open ERHerglotz ERDiscreteFourier ERFourierInverse ERCharacterAngle ERNearestNeighbor ERCyclicDecay ERCyclicSummation

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- Membership in the exact ER spectral domain forces a nonreal
spectral parameter, without any extra assumption on the height exponent. -/
theorem spectralDomain_im_ne_zero {p : Params} {κ ηExp C₀ : ℝ} {z : ℂ}
    (hz : ERSpectralDomain p κ ηExp C₀ z) : z.im ≠ 0 := by
  have hL : 0 < (p.L : ℝ) := by
    exact_mod_cast p.L_pos
  have hrpow : 0 < Real.rpow (p.L : ℝ) (-1 + ηExp) :=
    Real.rpow_pos_of_pos hL _
  have habs : 0 < |z.im| := lt_of_lt_of_le hrpow hz.1
  exact abs_pos.mp habs

end ERDeterministicMDECore
end GaussianRing
end BlockBand.Adapters.ErdosRiabov.CyclicModel
