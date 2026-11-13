module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.ComplexGammaLaplace

/-!
# Explicit two-dimensional transform of the APSSS ratio kernel

The two-dimensional Fourier transform of the regularized APSSS ratio kernel, computed slice by
slice and then by a complex-rate Gamma integral, with the normalization `Γ(3/2+δ)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Complex MeasureTheory Set
open scoped ENNReal NNReal Topology

/-- Evaluation of one transverse slice, including the longitudinal Fourier phase. -/
theorem integral_fourierRatioIntegrand_slice {ε δ ξ η x : ℝ}
    (hε : 0 < ε) :
    ∫ y : ℝ, fourierRatioIntegrand ε δ ξ η (x, y) =
      if 0 < x then
          ((2 * Real.sqrt Real.pi * ε : ℝ) : ℂ) *
          ((x ^ (δ + 1 / 2) : ℝ) : ℂ) *
          Complex.exp (-(x : ℂ) * fourierRatioLaplaceParameter ε δ ξ η)
      else 0 := by
  by_cases hx : 0 < x
  · rw [ite_eq_left hx]
    have hgauss := fourierRatioKernel_gaussian_slice_normalized hε hx η
    rw [show (∫ y : ℝ, fourierRatioIntegrand ε δ ξ η (x, y)) =
        ((Real.exp (-δ * x) * x ^ δ : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * (ξ : ℂ) * (x : ℂ))) *
          (∫ y : ℝ,
            Complex.exp (-(((y ^ 2 / (4 * ε ^ 2 * x) : ℝ) : ℂ))) *
              Complex.exp (-(Complex.I * (η : ℂ) * (y : ℂ))) ) by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      unfold fourierRatioIntegrand regularizedFourierRatioKernel
      rw [ite_eq_left hx]
      push_cast
      have hphase :
          Complex.exp (-(Complex.I * ((ξ : ℂ) * (x : ℂ) +
            (η : ℂ) * (y : ℂ)))) =
            Complex.exp (-(Complex.I * (ξ : ℂ) * (x : ℂ))) *
              Complex.exp (-(Complex.I * (η : ℂ) * (y : ℂ))) := by
        rw [← Complex.exp_add]
        congr 1
        ring
      rw [hphase]
      ring]
    rw [hgauss]
    have hxpow : Real.sqrt x * x ^ δ = x ^ (δ + 1 / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]
      congr 1
      ring
    have hexp :
        Complex.exp (-((δ * x : ℝ) : ℂ)) *
            Complex.exp (-(Complex.I * (ξ : ℂ) * (x : ℂ))) *
            Complex.exp (-((η ^ 2 * ε ^ 2 * x : ℝ) : ℂ)) =
          Complex.exp (-(x : ℂ) * fourierRatioLaplaceParameter ε δ ξ η) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      simp only [fourierRatioLaplaceParameter]
      push_cast
      ring
    rw [← hxpow] at *
    rw [← hexp]
    push_cast
    ring
  · rw [ite_eq_right hx]
    simp [fourierRatioIntegrand, regularizedFourierRatioKernel, hx]

/-- The remaining longitudinal integral is the complex-rate Gamma integral on the
principal branch. -/
theorem integral_fourierRatioIntegrand_iterated {ε δ ξ η : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) :
    ∫ x : ℝ, ∫ y : ℝ, fourierRatioIntegrand ε δ ξ η (x, y) =
      ((2 * Real.sqrt Real.pi * ε : ℝ) : ℂ) *
        (fourierRatioLaplaceParameter ε δ ξ η) ^
          (-(((3 / 2 + δ : ℝ)) : ℂ)) *
        Complex.Gamma (((3 / 2 + δ : ℝ)) : ℂ) := by
  simp_rw [integral_fourierRatioIntegrand_slice hε]
  rw [show (∫ x : ℝ, if 0 < x then
        ((2 * Real.sqrt Real.pi * ε : ℝ) : ℂ) *
        ((x ^ (δ + 1 / 2) : ℝ) : ℂ) *
        Complex.exp (-(x : ℂ) * fourierRatioLaplaceParameter ε δ ξ η) else 0) =
      ((2 * Real.sqrt Real.pi * ε : ℝ) : ℂ) *
        ∫ x : ℝ in Ioi 0,
          (x : ℂ) ^ ((((3 / 2 + δ : ℝ)) : ℂ) - 1) *
            Complex.exp (-(x : ℂ) * fourierRatioLaplaceParameter ε δ ξ η) by
    rw [← integral_indicator measurableSet_Ioi, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : 0 < x
    · rw [indicator_of_mem (show x ∈ Ioi 0 from hx), ite_eq_left hx]
      have hpow : ((x ^ (δ + 1 / 2) : ℝ) : ℂ) =
          (x : ℂ) ^ ((((3 / 2 + δ : ℝ)) : ℂ) - 1) := by
        rw [Complex.ofReal_cpow hx.le]
        congr 1
        push_cast
        ring
      rw [hpow]
      ring
    · rw [indicator_of_notMem (show x ∉ Ioi 0 from hx), ite_eq_right hx]
      simp]
  rw [complexGammaIntegral_eq
    (a := (((3 / 2 + δ : ℝ)) : ℂ))
    (w := fourierRatioLaplaceParameter ε δ ξ η)]
  · ring
  · simp
    linarith
  · exact fourierRatioLaplaceParameter_re_pos hδ

/-- The explicit two-dimensional Fourier transform in APSSS Claim 2, with exact
`Γ(3/2+δ)` normalization and principal-power denominator. -/
theorem fourier_hDelta {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (ξ η : ℝ) :
    ∫ p : ℝ × ℝ,
      (if 0 < p.1 then
        Real.exp (-(p.2 ^ 2) / (4 * ε ^ 2 * p.1)) * Real.exp (-δ * p.1) * p.1 ^ δ
      else 0) *
        Complex.exp (-(Complex.I * ((ξ : ℂ) * p.1 + (η : ℂ) * p.2))) =
      2 * Real.sqrt Real.pi * Real.Gamma (3 / 2 + δ) * ε /
        (((η ^ 2 * ε ^ 2 + δ : ℝ) : ℂ) + (ξ : ℂ) * Complex.I) ^
          (((3 / 2 + δ : ℝ)) : ℂ) := by
  change (∫ p : ℝ × ℝ, fourierRatioIntegrand ε δ ξ η p) = _
  rw [integral_fourierRatioIntegrand_prod hε hδ,
    integral_fourierRatioIntegrand_iterated hε hδ]
  rw [Complex.cpow_neg]
  rw [Complex.Gamma_ofReal]
  simp only [fourierRatioLaplaceParameter]
  push_cast
  field_simp

end PSSSNative.BlockBand.PSSS
