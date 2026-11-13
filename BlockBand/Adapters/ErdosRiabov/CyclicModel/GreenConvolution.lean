module

public import BlockBand.Adapters.ErdosRiabov.CyclicModel.FourierStabilityAlgebra
public import Mathlib

/-!
# Exact Fourier Green-kernel convolution

This module reconstructs the Fourier-defined scalar stability inverse as convolution
with the explicitly normalized cyclic Green kernel.  It is an exact finite identity;
no decay estimate or analytic certificate is assumed.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Adapters.ErdosRiabov.CyclicModel
namespace GaussianRing
namespace ERGreenConvolution

open scoped BigOperators
open ERProfile ERDiscreteFourier ERFourierInverse ERFourierAlgebra

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- Multiplicativity of the standard character combines the inverse-transform phase
with the DFT phase into the translation-invariant difference `x-y`. -/
theorem character_phase_difference (p : Params) (r x y : ZMod p.n) :
    ZMod.stdAddChar (r * x) * ZMod.stdAddChar (-(y * r)) =
      ZMod.stdAddChar (r * (x - y)) := by
  rw [← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- Exact Green-kernel convolution representation, with the source normalization
`1/n` and the cyclic difference `x-y`. -/
theorem scalarStabilityInverse_eq_green_convolution
    (p : Params) (α : ℂ) (f : ZMod p.n → ℂ) (x : ZMod p.n) :
    scalarStabilityInverse p α f x =
      ∑ y, fourierGreenKernel p α x y * f y := by
  rw [scalarStabilityInverse_apply]
  simp_rw [cyclicDFT_apply]
  unfold fourierGreenKernel
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro r hr
  rw [← character_phase_difference p r x y]
  ring

end ERGreenConvolution
end GaussianRing
end BlockBand.Adapters.ErdosRiabov.CyclicModel
