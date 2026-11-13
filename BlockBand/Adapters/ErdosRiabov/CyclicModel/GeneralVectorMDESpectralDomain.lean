module

public import BlockBand.Adapters.ErdosRiabov.CyclicModel.GeneralVectorMDECyclic
public import BlockBand.Adapters.ErdosRiabov.CyclicModel.ScalarProfileSourceFaithfulNormalization
public import BlockBand.Adapters.ErdosRiabov.CyclicModel.Clause1CyclicControl
public import BlockBand.Adapters.ErdosRiabov.CyclicModel.ProfileAdmissibility
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Basic.Complex.Basic
public import BlockBand.Adapters.ErdosRiabov.CyclicModel.CriticalSequences
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
public import BlockBand.Adapters.ErdosRiabov.CyclicModel.Conventions
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Probability.Independence.Integration
public import BlockBand.Adapters.ErdosRiabov.CyclicModel.ProfileAnalytic
public import Mathlib

/-!
# Localization-length decay of the ER kernels and the MDE assembly

This module proves for `Θ` the Fourier/recurrence rate `√η / 2` per block
(instead of the height-linear Neumann rate), i.e. the ER localization length
`W / √η` in sites, and assembles it with the general vector-MDE package and the
clause-(i) control bounds.

Source: Erdős–Riabov, *The Zigzag Strategy for Random Band Matrices*,
arXiv:2506.06441v1, ER (2.9), (2.10), (2.15), (2.18).
Normalization: `S = varianceProfile p` (row sums `1`), `m = erSemicircleStieltjes`,
`Θ = aS(1 - aS)⁻¹` with `a = m(z₁) conj m(z₂)`, `Ξ` with `a = m(z₁) m(z₂)`.

Results:

* `Θ`: an entrywise √η-localization bound for **every** pair of nonreal spectral
  parameters, with no spectral-domain, norm-cutoff, `κ`, or half-plane hypothesis.
  The height enters as `η = min 1 (min |Im z₁| |Im z₂|)`; constants are uniform
  in `n`, `W`, parity and the spectral parameters, and depend on `b` only through
  `jumpBondMargin p`.
* `Ξ`: the ER control bound used here is the fixed-bond one, on the ER domain with
  norm cutoff `C₀ = 1` and same half-plane.  The `κ`-dependent bound for an
  arbitrary cutoff is `ERGeneralVectorMDEXiKappa.norm_erXi_le_xi_kappa`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Adapters.ErdosRiabov.CyclicModel
namespace GaussianRing
namespace ERGeneralVectorMDESpectralDomain

open scoped BigOperators
open ERGeneralVectorMDE ERGeneralVectorMDECyclic ERCyclicDecay ERJumpNormalization ERPhysicalBridge ERHerglotz ERClause1 ERScalarProfileSourceFaithfulNormalization ERFourierInverse ERNearestNeighbor

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- The truncated height `η = min 1 (min |Im z₁| |Im z₂|)`. -/
def truncatedHeight (z₁ z₂ : ℂ) : ℝ := min 1 (min |z₁.im| |z₂.im|)

theorem truncatedHeight_pos {z₁ z₂ : ℂ} (h₁ : z₁.im ≠ 0) (h₂ : z₂.im ≠ 0) :
    0 < truncatedHeight z₁ z₂ :=
  lt_min one_pos (lt_min (abs_pos.mpr h₁) (abs_pos.mpr h₂))

/-- The Fourier/recurrence `√η` block decay of the corrected-`Θ` Green kernel,
for all nonreal `z₁, z₂` (no domain hypothesis). -/
theorem norm_fourierGreenKernel_theta_le_sqrt_height (p : Params) {z₁ z₂ : ℂ}
    (h₁ : z₁.im ≠ 0) (h₂ : z₂.im ≠ 0) (k l : ZMod p.n) :
    ‖fourierGreenKernel p
        (erSemicircleStieltjes z₁ * starRingEnd ℂ (erSemicircleStieltjes z₂)) k l‖ ≤
      16 * Real.exp (-(Real.sqrt (truncatedHeight z₁ z₂) / 2) *
          cyclicBlockDistance p k l) /
        (min 1 ((p.n : ℝ) * Real.sqrt (truncatedHeight z₁ z₂)) *
          Real.sqrt (truncatedHeight z₁ z₂) * Real.sqrt (jumpBondMargin p)) := by
  have hm₁0 : erSemicircleStieltjes z₁ ≠ 0 := by
    intro hm
    have h := erSemicircleStieltjes_dyson z₁
    simp [hm] at h
  have hm₂0 : erSemicircleStieltjes z₂ ≠ 0 := by
    intro hm
    have h := erSemicircleStieltjes_dyson z₂
    simp [hm] at h
  have hα0 : erSemicircleStieltjes z₁ * starRingEnd ℂ (erSemicircleStieltjes z₂) ≠ 0 :=
    mul_ne_zero hm₁0 ((map_ne_zero (starRingEnd ℂ)).2 hm₂0)
  have hα := norm_thetaMultiplier_lt_one
    (norm_erSemicircleStieltjes_lt_one h₁) (norm_erSemicircleStieltjes_lt_one h₂)
  have hη0 := truncatedHeight_pos h₁ h₂
  have hη1 : truncatedHeight z₁ z₂ ≤ 1 := min_le_left _ _
  have hmargin : truncatedHeight z₁ z₂ / 4 ≤
      1 - ‖erSemicircleStieltjes z₁ * starRingEnd ℂ (erSemicircleStieltjes z₂)‖ := by
    have h := thetaMultiplier_height_margin h₁ h₂
    have hle : truncatedHeight z₁ z₂ ≤ min |z₁.im| |z₂.im| := min_le_right _ _
    have : truncatedHeight z₁ z₂ / 4 ≤ min (1 / 2 : ℝ) (min |z₁.im| |z₂.im| / 4) :=
      le_min (by linarith) (by linarith)
    linarith
  exact norm_fourierGreenKernel_le_theta_height p hα0 hα hη0 hη1 hmargin k l

/-- **`Θ` localization-length decay** (ER (2.10), every `Params p`, every
nonreal `z₁, z₂`, every pair of sites).  With `η = min 1 (min |Im z₁| |Im z₂|)`
and `d` the cyclic block distance,
`‖Θ(z₁,z₂)_xy‖ ≤ (16 e^{-(√η/2) d} / (min(1, n√η) √η √(jumpBondMargin p))
  + 1_{x.1 = y.1}) / W`.
The decay length is `2/√η` blocks, i.e. the ER localization length `W/√η` up
to the factor two. -/
theorem norm_erTheta_le_sqrt_height (p : Params) {z₁ z₂ : ℂ}
    (h₁ : z₁.im ≠ 0) (h₂ : z₂.im ≠ 0) (x y : Site p.n p.W) :
    ‖erTheta p z₁ z₂ x y‖ ≤
      (16 * Real.exp (-(Real.sqrt (truncatedHeight z₁ z₂) / 2) *
          cyclicBlockDistance p x.1 y.1) /
        (min 1 ((p.n : ℝ) * Real.sqrt (truncatedHeight z₁ z₂)) *
          Real.sqrt (truncatedHeight z₁ z₂) * Real.sqrt (jumpBondMargin p)) +
        (if x.1 = y.1 then 1 else 0)) / (p.W : ℝ) := by
  rw [erTheta_apply_eq_siteGreenKernel_sub_identity p h₁ h₂ x y,
    norm_siteGreenKernel_sub_identity]
  apply div_le_div_of_nonneg_right _ (by positivity)
  refine (norm_sub_le _ _).trans (add_le_add
    (norm_fourierGreenKernel_theta_le_sqrt_height p h₁ h₂ x.1 y.1) ?_)
  split_ifs <;> simp

end ERGeneralVectorMDESpectralDomain
end GaussianRing
end BlockBand.Adapters.ErdosRiabov.CyclicModel
