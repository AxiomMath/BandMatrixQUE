module

public import BlockBand.Adapters.ErdosRiabov.CyclicModel.FourierStabilityInverse
public import Mathlib

/-!
# Algebraic completion of the cyclic Fourier stability inverse

The covariance eigenvalues `1 - 2b(1 - cos θ)` have modulus at most one, so the
multiplier `1 - α λ_r` is nonzero for `‖α‖ < 1`, and the Fourier stability inverse is a
two-sided inverse of the diagonal Fourier stability operator.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Adapters.ErdosRiabov.CyclicModel
namespace GaussianRing
namespace ERFourierAlgebra

open ERProfile ERProfileAnalytic ERDiscreteFourier ERFourierInverse

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- The cyclic symbol as a function of the cosine coordinate. -/
def cyclicSymbolCos (b u : ℝ) : ℝ := 1 - 2 * b * (1 - u)

/-- The covariance eigenvalue is exactly the cyclic symbol of its character
cosine coordinate. -/
theorem covarianceEigenvalue_eq_cyclicSymbolCos (p : Params) (r : ZMod p.n) :
    covarianceEigenvalue p r =
      (cyclicSymbolCos p.b (characterCosine p r) : ℝ) := by
  rw [covarianceEigenvalue_eq_characterSymbol]
  unfold cyclicSymbolCos
  rw [show p.c = 1 - 2 * p.b by linarith [p.c_add_two_b]]
  ring

/-- A standard cyclic character has unit norm. -/
theorem norm_stdAddChar (p : Params) (r : ZMod p.n) :
    ‖ZMod.stdAddChar r‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

/-- Character cosines lie in `[-1,1]`. -/
theorem abs_characterCosine_le_one (p : Params) (r : ZMod p.n) :
    |characterCosine p r| ≤ 1 := by
  calc
    |characterCosine p r| ≤ ‖ZMod.stdAddChar r‖ := Complex.abs_re_le_norm _
    _ = 1 := norm_stdAddChar p r

/-- Every covariance eigenvalue lies in the closed unit disk. -/
theorem norm_covarianceEigenvalue_le_one (p : Params) (r : ZMod p.n) :
    ‖covarianceEigenvalue p r‖ ≤ 1 := by
  rw [covarianceEigenvalue_eq_cyclicSymbolCos]
  rw [Complex.norm_real]
  rw [Real.norm_eq_abs]
  rw [abs_le]
  constructor
  · have hc := abs_characterCosine_le_one p r
    rw [abs_le] at hc
    unfold cyclicSymbolCos
    nlinarith [p.b_pos.le, p.b_lt_half]
  · unfold cyclicSymbolCos
    have hc := abs_characterCosine_le_one p r
    rw [abs_le] at hc
    nlinarith [p.b_pos.le]

/-- The stability multiplier is nonzero throughout the explicit disk `‖α‖<1`. -/
theorem stabilityMultiplier_ne_zero (p : Params) {α : ℂ} (hα : ‖α‖ < 1)
    (r : ZMod p.n) : stabilityMultiplier p α r ≠ 0 := by
  intro h
  have heq : α * covarianceEigenvalue p r = 1 :=
    (sub_eq_zero.mp h).symm
  have hn := norm_covarianceEigenvalue_le_one p r
  have ha := norm_nonneg α
  have hmul : ‖α * covarianceEigenvalue p r‖ < 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg (covarianceEigenvalue p r)]
  rw [heq, norm_one] at hmul
  exact (lt_irrefl 1 hmul)

/-- The stability operator in Fourier coordinates. -/
def fourierStabilityOperator (p : Params) (α : ℂ) (f : ZMod p.n → ℂ) :
    ZMod p.n → ℂ :=
  (cyclicDFT p).symm (fun r => stabilityMultiplier p α r * cyclicDFT p f r)

/-- Left inverse identity for the Fourier-defined stability inverse. -/
theorem scalarStabilityInverse_left (p : Params) {α : ℂ} (hα : ‖α‖ < 1)
    (f : ZMod p.n → ℂ) :
    scalarStabilityInverse p α (fourierStabilityOperator p α f) = f := by
  apply (cyclicDFT p).injective
  ext r
  simp [scalarStabilityInverse, fourierStabilityOperator,
    inverseStabilityMultiplier, stabilityMultiplier_ne_zero p hα r]

/-- Right inverse identity for the Fourier-defined stability inverse. -/
theorem scalarStabilityInverse_right (p : Params) {α : ℂ} (hα : ‖α‖ < 1)
    (f : ZMod p.n → ℂ) :
    fourierStabilityOperator p α (scalarStabilityInverse p α f) = f := by
  apply (cyclicDFT p).injective
  ext r
  simp [scalarStabilityInverse, fourierStabilityOperator,
    inverseStabilityMultiplier, stabilityMultiplier_ne_zero p hα r]

end ERFourierAlgebra
end GaussianRing
end BlockBand.Adapters.ErdosRiabov.CyclicModel
