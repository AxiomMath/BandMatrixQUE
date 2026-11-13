module

public import Mathlib
public import BlockBand.GaussianCalculus.MultivariateIBP

/-!
# Multivariate circular weak Gaussian integration by parts

For `x ~ gaussianProduct v` with two coordinates `a ≠ b` of variance `t/2` and weak partial
derivatives `ga`, `gb` of `f`, the complex coordinate `x_a ± i x_b` satisfies
`E[(x_a ± i x_b) f] = t · E[(ga ± i gb)/2]` (`multivariateCircularGaussianIBP_holds`).
Together with the real identity this gives `GaussianIdentitiesMultivariate`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.GaussianCalculus

open MeasureTheory ProbabilityTheory Filter
open BlockBand.Internal.Contracts.Inputs
open scoped NNReal

/-- A real multiplier dominated in absolute value by `‖Z‖` inherits integrability from
`Z f`. -/
theorem integrable_real_smul_of_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {f : X → ℂ} (hf : AEStronglyMeasurable f μ) (u : X → ℝ) (hu : Measurable u)
    (Z : X → ℂ) (hZ : Integrable (fun x => Z x * f x) μ) (hle : ∀ x, |u x| ≤ ‖Z x‖) :
    Integrable (fun x => u x • f x) μ := by
  apply hZ.norm.mono' (hu.aestronglyMeasurable.smul hf)
  exact Filter.Eventually.of_forall fun x => by
    change ‖u x • f x‖ ≤ ‖Z x * f x‖
    rw [norm_smul, norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hle x) (norm_nonneg _)

/-- , for a circular coordinate, as the contract
`Internal.Contracts.Inputs.MultivariateCircularGaussianIBP`.
Law `gaussianProduct v` on
`ι → ℝ` (finite `ι`);
`a ≠ b` with `v a = v b = t/2`, every other coordinate of positive
variance;
`f:
(ι → ℝ) → ℂ` with distributional weak partials `ga`, `gb` in coordinates
`a`, `b`;
Gaussian integrability of `f`, `ga`, `gb` and of the relevant coordinate product.
Conclusions `E[Z f] = t E[(ga + i gb)/2]` and `E[Z̄ f] = t E[(ga - i gb)/2]`,
`Z = x_a + i x_b`.
Uses `multivariateGaussianIBP_of_ne_zero` and `ae_gaussianProduct_coord_eq_zero`.
-/
theorem multivariateCircularGaussianIBP_holds : MultivariateCircularGaussianIBP := by
  intro ι _ _ v a b t hv hab hva hvb f ga gb hwa hwb hf hga hgb
  by_cases ht : t = 0
  · have hae := ae_gaussianProduct_coord_eq_zero v a (by rw [hva, ht, zero_div])
    have hbe := ae_gaussianProduct_coord_eq_zero v b (by rw [hvb, ht, zero_div])
    refine ⟨fun _ => ?_, fun _ => ?_⟩
    · have hz : (fun x : ι → ℝ => ((x a : ℂ) + (x b : ℂ) * Complex.I) * f x)
          =ᵐ[gaussianProduct v] fun _ => 0 := by
        filter_upwards [hae, hbe] with x h1 h2
        simp [h1, h2]
      rw [integral_congr_ae hz, integral_zero, ht]
      simp
    · have hz : (fun x : ι → ℝ => ((x a : ℂ) - (x b : ℂ) * Complex.I) * f x)
          =ᵐ[gaussianProduct v] fun _ => 0 := by
        filter_upwards [hae, hbe] with x h1 h2
        simp [h1, h2]
      rw [integral_congr_ae hz, integral_zero, ht]
      simp
  have ht2 : t / 2 ≠ 0 := div_ne_zero ht (by norm_num)
  have hpos : ∀ j, v j ≠ 0 := fun j => by
    by_cases hja : j = a
    · rw [hja, hva]
      exact ht2
    by_cases hjb : j = b
    · rw [hjb, hvb]
      exact ht2
    exact (hv j hja hjb).ne'
  have hra := multivariateGaussianIBP_of_ne_zero v hpos a hwa hf hga
  have hrb := multivariateGaussianIBP_of_ne_zero v hpos b hwb hf hgb
  have hfm := hf.aestronglyMeasurable
  have hvaR : ((v a : ℝ≥0) : ℝ) = (t : ℝ) / 2 := by
    rw [hva, NNReal.coe_div, NNReal.coe_ofNat]
  have hvbR : ((v b : ℝ≥0) : ℝ) = (t : ℝ) / 2 := by
    rw [hvb, NNReal.coe_div, NNReal.coe_ofNat]
  constructor
  · intro hZ
    have hxa : Integrable (fun x : ι → ℝ => x a • f x) (gaussianProduct v) :=
      integrable_real_smul_of_le _ hfm _ (measurable_pi_apply a) _ hZ fun x => by
        simpa using Complex.abs_re_le_norm ((x a : ℂ) + (x b : ℂ) * Complex.I)
    have hxb : Integrable (fun x : ι → ℝ => x b • f x) (gaussianProduct v) :=
      integrable_real_smul_of_le _ hfm _ (measurable_pi_apply b) _ hZ fun x => by
        simpa using Complex.abs_im_le_norm ((x a : ℂ) + (x b : ℂ) * Complex.I)
    have he (x : ι → ℝ) : ((x a : ℂ) + (x b : ℂ) * Complex.I) * f x =
        x a • f x + Complex.I * (x b • f x) := by
      simp only [Complex.real_smul]
      ring
    simp_rw [he]
    rw [integral_add hxa (hxb.const_mul Complex.I), integral_const_mul, hra hxa, hrb hxb,
      integral_div, integral_add hga (hgb.const_mul Complex.I), integral_const_mul, hvaR, hvbR]
    simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_ofNat]
    ring
  · intro hZ
    have hxa : Integrable (fun x : ι → ℝ => x a • f x) (gaussianProduct v) :=
      integrable_real_smul_of_le _ hfm _ (measurable_pi_apply a) _ hZ fun x => by
        simpa using Complex.abs_re_le_norm ((x a : ℂ) - (x b : ℂ) * Complex.I)
    have hxb : Integrable (fun x : ι → ℝ => x b • f x) (gaussianProduct v) :=
      integrable_real_smul_of_le _ hfm _ (measurable_pi_apply b) _ hZ fun x => by
        simpa using Complex.abs_im_le_norm ((x a : ℂ) - (x b : ℂ) * Complex.I)
    have he (x : ι → ℝ) : ((x a : ℂ) - (x b : ℂ) * Complex.I) * f x =
        x a • f x - Complex.I * (x b • f x) := by
      simp only [Complex.real_smul]
      ring
    simp_rw [he]
    rw [integral_sub hxa (hxb.const_mul Complex.I), integral_const_mul, hra hxa, hrb hxb,
      integral_div, integral_sub hga (hgb.const_mul Complex.I), integral_const_mul, hvaR, hvbR]
    simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_ofNat]
    ring

/-- The real and circular Gaussian integration-by-parts identities for functions of the whole
Gaussian vector under `gaussianProduct v` (`GaussianIdentitiesMultivariate`). -/
theorem gaussianIdentitiesMultivariate_holds : GaussianIdentitiesMultivariate :=
  ⟨multivariateGaussianIBP_holds, multivariateCircularGaussianIBP_holds⟩

end BlockBand.GaussianCalculus
