module

public import BlockBand.Adapters.ErdosRiabov.CyclicModel.DiscreteFourierGreen
public import Mathlib

/-!
# Fourier stability inverse for the cyclic profile

Defines the character cosine, the principal frequency and angle of a mode of `ZMod n`, with
`|θ| ≤ π` and a quadratic gap bound, and the scalar stability inverse as the inverse DFT of
the inverse stability multiplier, written as convolution with a Fourier Green kernel.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Adapters.ErdosRiabov.CyclicModel
namespace GaussianRing
namespace ERFourierInverse

open scoped BigOperators
open ERProfile ERProfileAnalytic ERDiscreteFourier

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- The cosine coordinate of a discrete character. -/
def characterCosine (p : Params) (r : ZMod p.n) : ℝ :=
  (ZMod.stdAddChar r).re

/-- The complex covariance eigenvalue is real and is the cyclic symbol evaluated at
the character's cosine coordinate. -/
theorem covarianceEigenvalue_eq_characterSymbol (p : Params) (r : ZMod p.n) :
    covarianceEigenvalue p r =
      (p.c + 2 * p.b * characterCosine p r : ℝ) := by
  rw [covarianceEigenvalue, AddChar.map_neg_eq_conj]
  apply Complex.ext
  · simp [characterCosine]
    ring
  · simp

/-- Unoriented principal frequency.  For an even ring it includes the unique antipode;
for an odd ring its maximum is `(n-1)/2`. -/
def principalFrequency (p : Params) (r : ZMod p.n) : ℕ :=
  min r.val (p.n - r.val)

/-- Principal discrete angle in `[0,π]`. -/
def principalAngle (p : Params) (r : ZMod p.n) : ℝ :=
  2 * Real.pi * principalFrequency p r / p.n

/-- Parity-independent half-ring bound; equality is possible exactly at an even
antipode. -/
theorem two_mul_principalFrequency_le (p : Params) (r : ZMod p.n) :
    2 * principalFrequency p r ≤ p.n := by
  unfold principalFrequency
  have hr := r.val_lt
  omega

/-- Every principal angle lies in the interval used by the quadratic cosine bound. -/
theorem abs_principalAngle_le_pi (p : Params) (r : ZMod p.n) :
    |principalAngle p r| ≤ Real.pi := by
  have hn : 0 < (p.n : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 4) p.n_ge_four
  have hq : (2 * principalFrequency p r : ℝ) ≤ p.n := by
    exact_mod_cast two_mul_principalFrequency_le p r
  have hnonneg : 0 ≤ principalAngle p r := by
    unfold principalAngle
    positivity
  rw [abs_of_nonneg hnonneg]
  unfold principalAngle
  apply (div_le_iff₀ hn).2
  nlinarith [Real.pi_pos]

/-- Fixed-coupling quantitative nonconstant-mode gap, valid at the even antipode and
through the full odd frequency range. -/
theorem principalAngle_quadratic_gap (p : Params) (r : ZMod p.n) :
    (4 * p.b / Real.pi ^ 2) * principalAngle p r ^ 2 ≤
      1 - cyclicSymbol p.b (principalAngle p r) :=
  cyclicSymbol_quadratic_gap p.b_pos.le (abs_principalAngle_le_pi p r)

/-- Explicit inverse DFT, including the `1/n` normalization and positive character. -/
theorem inverseDFT_apply (p : Params) (g : ZMod p.n → ℂ) (x : ZMod p.n) :
    (cyclicDFT p).symm g x =
      (p.n : ℂ)⁻¹ * ∑ r, ZMod.stdAddChar (r * x) * g r := by
  simp [cyclicDFT, ZMod.invDFT_apply, smul_eq_mul]

/-- Modewise inverse multiplier for `I-αC`. -/
def inverseStabilityMultiplier (p : Params) (α : ℂ) (r : ZMod p.n) : ℂ :=
  (stabilityMultiplier p α r)⁻¹

/-- Fourier-defined scalar stability inverse. -/
def scalarStabilityInverse (p : Params) (α : ℂ) (f : ZMod p.n → ℂ) :
    ZMod p.n → ℂ :=
  (cyclicDFT p).symm (fun r => inverseStabilityMultiplier p α r * cyclicDFT p f r)

/-- Explicit Fourier Green kernel. -/
def fourierGreenKernel (p : Params) (α : ℂ) (x y : ZMod p.n) : ℂ :=
  (p.n : ℂ)⁻¹ * ∑ r,
    ZMod.stdAddChar (r * (x - y)) * inverseStabilityMultiplier p α r

/-- Explicit inverse formula before rewriting it as convolution by the Green kernel. -/
theorem scalarStabilityInverse_apply (p : Params) (α : ℂ)
    (f : ZMod p.n → ℂ) (x : ZMod p.n) :
    scalarStabilityInverse p α f x =
      (p.n : ℂ)⁻¹ * ∑ r, ZMod.stdAddChar (r * x) *
        (inverseStabilityMultiplier p α r * cyclicDFT p f r) := by
  exact inverseDFT_apply p _ x

end ERFourierInverse
end GaussianRing
end BlockBand.Adapters.ErdosRiabov.CyclicModel
