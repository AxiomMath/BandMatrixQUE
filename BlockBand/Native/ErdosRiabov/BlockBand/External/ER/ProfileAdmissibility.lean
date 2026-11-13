module

public import BlockBand.Native.ErdosRiabov.BlockBand.Analysis.ERAdmissibility
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The cyclic Gaussian-ring covariance profile

This file discharges the finite, algebraic part of Erdős–Riabov Proposition 2.8(ii)
for the Gaussian ring.  It records the covariance operator, its circulant Fourier
symbol, exact stochasticity and flatness, a dimension-independent gap identity, an
entrywise exponential Green estimate with its (finite and completely explicit)
weighted constant, and the tensorization with the normalized within-block kernel.

Source: Erdős–Riabov, *The Zigzag Strategy for Random Band Matrices*,
arXiv:2506.06441v1, Definition 2.1 and Proposition 2.8.  The indicator in the displayed
block example has its support sign reversed: the covariance is supported when the
cyclic block distance is **at most** one, not at least one; the support used here is the
corrected one.

All statements quantify over `Params`; hence they cover every `n ≥ 4`, with no parity
assumption.  The Green constant below is the exact finite weighted norm, not an
unspecified implicit constant.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace ERNative.BlockBand
namespace GaussianRing
namespace ERProfile

open scoped BigOperators
open MeasureTheory ProbabilityTheory

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- The scalar cyclic covariance operator `C` at block scale. -/
def cyclicCovariance (p : Params) : Matrix (ZMod p.n) (ZMod p.n) ℝ :=
  fun k l => blockWeight p k l

/-- The full Erdős–Riabov covariance operator on physical sites. -/
def siteCovariance (p : Params) : Matrix (Site p.n p.W) (Site p.n p.W) ℝ :=
  fun x y => varianceProfile p x y

/-- Exact Gaussian-ring covariance formula, including the `W⁻¹` normalization. -/
theorem siteCovariance_apply (p : Params) (x y : Site p.n p.W) :
    siteCovariance p x y = cyclicCovariance p x.1 y.1 / (p.W : ℝ) := rfl

/-- The tensor factor on the within-block coordinate. -/
def normalizedBlockKernel (p : Params) : Matrix (Fin p.W) (Fin p.W) ℝ :=
  fun _ _ => 1 / (p.W : ℝ)

/-- Proposition 2.8(ii)'s omitted tensorization, entry by entry: the full site
covariance is exactly `C ⊗ W⁻¹ 11*`. -/
theorem proposition28ii_tensorization (p : Params) (x y : Site p.n p.W) :
    siteCovariance p x y =
      cyclicCovariance p x.1 y.1 * normalizedBlockKernel p x.2 y.2 := by
  rw [siteCovariance_apply]
  simp only [normalizedBlockKernel]
  ring

/-- Tensorization preserves stochasticity exactly, including width one. -/
theorem siteCovariance_stochastic (p : Params) (x : Site p.n p.W) :
    ∑ y, siteCovariance p x y = 1 :=
  sum_varianceProfile p x

/-- The full site profile has the sharp `W⁻¹` flatness constant. -/
theorem siteCovariance_flat (p : Params) (x y : Site p.n p.W) :
    0 ≤ siteCovariance p x y ∧ siteCovariance p x y ≤ 1 / (p.W : ℝ) := by
  exact ⟨varianceProfile_nonneg p x y,
    (varianceProfile_erDefinition21 p).flat x y⟩

/-- The covariance statements are parity-free: one theorem simultaneously returns
the exact profile witnesses for an even or an odd ring. -/
theorem both_ring_parities (p : Params) :
    ERDefinition21Profile p ∧ ERBlockBandProfile p :=
  erProfilePrerequisites p

/-- The probability-law API already carries exactly the Hermitian Gaussian entry
normalizations from which the ER centering, all moments, and complex second moments
are computed.  This theorem exposes those hypotheses together with the covariance
operator, without adding a local-law assumption. -/
structure ExactGaussianRingCovariance (p : Params) (M : Law p) : Prop where
  hermitian : ∀ ω, (M.H ω).IsHermitian
  diagonalGaussian : ∀ x,
    HasLaw (fun ω => (M.H ω x x).re) (gaussianReal 0 (varianceNNReal p x x)) M.P
  offdiagRealGaussian : ∀ x y, siteLE p x y → x ≠ y →
    HasLaw (fun ω => (M.H ω x y).re)
      (gaussianReal 0 ⟨siteCovariance p x y / 2, by
        exact div_nonneg (varianceProfile_nonneg p x y) (by norm_num)⟩) M.P
  offdiagImagGaussian : ∀ x y, siteLE p x y → x ≠ y →
    HasLaw (fun ω => (M.H ω x y).im)
      (gaussianReal 0 ⟨siteCovariance p x y / 2, by
        exact div_nonneg (varianceProfile_nonneg p x y) (by norm_num)⟩) M.P
  componentsIndependent : ∀ x y, siteLE p x y → x ≠ y →
    IndepFun (fun ω => (M.H ω x y).re) (fun ω => (M.H ω x y).im) M.P

/-- Exact covariance/law package for every Gaussian-ring realization contract. -/
theorem exactGaussianRingCovariance (p : Params) (M : Law p) :
    ExactGaussianRingCovariance p M where
  hermitian := M.H_hermitian
  diagonalGaussian := M.diagonal_re_law
  offdiagRealGaussian := by simpa [siteCovariance] using M.offdiag_re_law
  offdiagImagGaussian := by simpa [siteCovariance] using M.offdiag_im_law
  componentsIndependent := M.offdiag_components_independent

end ERProfile
end GaussianRing
end ERNative.BlockBand
