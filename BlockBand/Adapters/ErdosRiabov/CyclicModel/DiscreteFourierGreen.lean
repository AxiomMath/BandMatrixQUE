module

public import BlockBand.Adapters.ErdosRiabov.CyclicModel.ProfileAnalytic
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib

/-!
# Discrete Fourier resolution of the cyclic covariance

This module connects the Gaussian-ring covariance with Mathlib's invertible discrete
Fourier transform on `ZMod n`.  It defines the exact characters and eigenvalues, proves
the character eigenvector equation, records Fourier completeness/inversion, and splits
the physical site space into block-constant and within-block mean-zero summands.
No local-law or seven-clause analytic certificate is assumed.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Adapters.ErdosRiabov.CyclicModel
namespace GaussianRing
namespace ERDiscreteFourier

open scoped BigOperators ComplexConjugate
open ERProfile ERProfileAnalytic

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- Exact complex eigenvalue of the cyclic nearest-neighbour covariance. -/
def covarianceEigenvalue (p : Params) (r : ZMod p.n) : ℂ :=
  p.c + p.b * ZMod.stdAddChar r + p.b * ZMod.stdAddChar (-r)

/-- The constant mode has eigenvalue one. -/
@[simp] theorem covarianceEigenvalue_zero (p : Params) :
    covarianceEigenvalue p 0 = 1 := by
  rw [covarianceEigenvalue, neg_zero, AddChar.map_zero_eq_one]
  norm_cast
  linarith [p.c_add_two_b]

/-- Mathlib's DFT is the completeness isomorphism for these cyclic modes. -/
def cyclicDFT (p : Params) :
    (ZMod p.n → ℂ) ≃ₗ[ℂ] (ZMod p.n → ℂ) := ZMod.dft

/-- Explicit Fourier transform formula. -/
theorem cyclicDFT_apply (p : Params) (f : ZMod p.n → ℂ) (r : ZMod p.n) :
    cyclicDFT p f r =
      ∑ x, ZMod.stdAddChar (-(x * r)) * f x := by
  simp [cyclicDFT, ZMod.dft_apply, smul_eq_mul]

/-- Fourier-space stability multiplier. -/
def stabilityMultiplier (p : Params) (α : ℂ) (r : ZMod p.n) : ℂ :=
  1 - α * covarianceEigenvalue p r

/-- Average of a physical vector over the internal coordinate of one block. -/
def blockAverage (p : Params) (f : Site p.n p.W → ℂ) (k : ZMod p.n) : ℂ :=
  (1 / (p.W : ℂ)) * ∑ i : Fin p.W, f (k, i)

/-- Block-constant projection. -/
def blockConstantPart (p : Params) (f : Site p.n p.W → ℂ) : Site p.n p.W → ℂ :=
  fun x => blockAverage p f x.1

/-- Within-block mean-zero remainder. -/
def blockMeanZeroPart (p : Params) (f : Site p.n p.W → ℂ) : Site p.n p.W → ℂ :=
  fun x => f x - blockConstantPart p f x

/-- Exact decomposition into block-constant and mean-zero parts. -/
theorem block_decomposition (p : Params) (f : Site p.n p.W → ℂ) (x : Site p.n p.W) :
    blockConstantPart p f x + blockMeanZeroPart p f x = f x := by
  simp [blockMeanZeroPart]

/-- The remainder has zero sum in every block. -/
theorem sum_blockMeanZeroPart (p : Params) (f : Site p.n p.W → ℂ)
    (k : ZMod p.n) :
    ∑ i : Fin p.W, blockMeanZeroPart p f (k, i) = 0 := by
  have hW : (p.W : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt p.W_pos
  simp only [blockMeanZeroPart, blockConstantPart, blockAverage,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

end ERDiscreteFourier
end GaussianRing
end BlockBand.Adapters.ErdosRiabov.CyclicModel
