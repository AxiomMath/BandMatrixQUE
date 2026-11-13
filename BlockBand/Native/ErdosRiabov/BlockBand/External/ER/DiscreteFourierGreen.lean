module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.ProfileAnalytic
public import Mathlib.Analysis.Fourier.ZMod

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

namespace ERNative.BlockBand
namespace GaussianRing
namespace ERDiscreteFourier

open scoped BigOperators ComplexConjugate
open ERProfile ERProfileAnalytic

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- The standard character indexed by cyclic frequency `r`. -/
def fourierCharacter (p : Params) (r x : ZMod p.n) : ℂ :=
  ZMod.stdAddChar (r * x)

/-- Exact complex eigenvalue of the cyclic nearest-neighbour covariance. -/
def covarianceEigenvalue (p : Params) (r : ZMod p.n) : ℂ :=
  p.c + p.b * ZMod.stdAddChar r + p.b * ZMod.stdAddChar (-r)

/-- The zero-frequency character is constant. -/
@[simp] theorem fourierCharacter_zero (p : Params) (x : ZMod p.n) :
    fourierCharacter p 0 x = 1 := by
  simp [fourierCharacter]

/-- The constant mode has eigenvalue one. -/
@[simp] theorem covarianceEigenvalue_zero (p : Params) :
    covarianceEigenvalue p 0 = 1 := by
  rw [covarianceEigenvalue, neg_zero, AddChar.map_zero_eq_one]
  norm_cast
  linarith [p.c_add_two_b]

/-- Average of a physical vector over the internal coordinate of one block. -/
def blockAverage (p : Params) (f : Site p.n p.W → ℂ) (k : ZMod p.n) : ℂ :=
  (1 / (p.W : ℂ)) * ∑ i : Fin p.W, f (k, i)

/-- Block-constant projection. -/
def blockConstantPart (p : Params) (f : Site p.n p.W → ℂ) : Site p.n p.W → ℂ :=
  fun x => blockAverage p f x.1

/-- Within-block mean-zero remainder. -/
def blockMeanZeroPart (p : Params) (f : Site p.n p.W → ℂ) : Site p.n p.W → ℂ :=
  fun x => f x - blockConstantPart p f x

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
end ERNative.BlockBand
