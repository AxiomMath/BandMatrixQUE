module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.FourierRatioFubini

/-!
# Fubini for the regularized APSSS kernel

The regularized Fourier integrand of the APSSS ratio kernel is measurable and absolutely
integrable on the product space, so its double integral may be computed in either order.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Complex MeasureTheory Set
open scoped ENNReal NNReal Topology

/-- The regularized APSSS Fourier integrand is measurable on the product space. -/
theorem measurable_fourierRatioIntegrand (ε δ ξ η : ℝ) :
    Measurable (fourierRatioIntegrand ε δ ξ η) := by
  unfold fourierRatioIntegrand regularizedFourierRatioKernel
  apply Measurable.mul
  · apply Complex.continuous_ofReal.measurable.comp
    apply Measurable.ite
    · exact measurableSet_lt measurable_const measurable_fst
    · measurability
    · exact measurable_const
  · fun_prop

/-- Every transverse slice of the regularized APSSS Fourier integrand is integrable. -/
theorem integrable_fourierRatioIntegrand_slice {ε δ ξ η x : ℝ}
    (hε : 0 < ε) :
    Integrable (fun y : ℝ => fourierRatioIntegrand ε δ ξ η (x, y)) := by
  have hmeas : AEStronglyMeasurable
      (fun y : ℝ => fourierRatioIntegrand ε δ ξ η (x, y)) :=
    ((measurable_fourierRatioIntegrand ε δ ξ η).comp
      measurable_prodMk_left).aestronglyMeasurable
  apply (integrable_norm_iff hmeas).mp
  rw [show (fun y : ℝ => ‖fourierRatioIntegrand ε δ ξ η (x, y)‖) =
      (fun y : ℝ => |regularizedFourierRatioKernel ε δ x y|) by
    funext y
    exact norm_fourierRatioIntegrand ε δ ξ η (x, y)]
  by_cases hx : 0 < x
  · have hb : 0 < 1 / (4 * ε ^ 2 * x) := by positivity
    have hg : Integrable (fun y : ℝ =>
        Real.exp (-(1 / (4 * ε ^ 2 * x)) * y ^ 2)) :=
      integrable_exp_neg_mul_sq hb
    have hk := hg.mul_const (Real.exp (-δ * x) * x ^ δ)
    apply hk.congr
    filter_upwards with y
    have hnonneg : 0 ≤ regularizedFourierRatioKernel ε δ x y := by
      simp [regularizedFourierRatioKernel, hx]
      positivity
    rw [abs_of_nonneg hnonneg]
    simp only [regularizedFourierRatioKernel, hx, ite_true]
    have he :
        -y ^ 2 / (4 * ε ^ 2 * x) =
          -(1 / (4 * ε ^ 2 * x)) * y ^ 2 := by
      field_simp
    rw [he]
    ring
  · simp [regularizedFourierRatioKernel, hx]

/-- Absolute product integrability of the regularized APSSS kernel. -/
theorem integrable_fourierRatioIntegrand {ε δ ξ η : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) :
    Integrable (fourierRatioIntegrand ε δ ξ η) (volume.prod volume) := by
  apply (integrable_prod_iff
    (measurable_fourierRatioIntegrand ε δ ξ η).aestronglyMeasurable).2
  constructor
  · exact ae_of_all _ fun x => integrable_fourierRatioIntegrand_slice hε
  · have hout := integrable_fourierRatio_norm_slice hε hδ
    apply hout.congr
    filter_upwards with x
    rw [show (∫ y : ℝ, ‖fourierRatioIntegrand ε δ ξ η (x, y)‖) =
      ∫ y : ℝ, |regularizedFourierRatioKernel ε δ x y| by
        congr 1
        funext y
        exact norm_fourierRatioIntegrand ε δ ξ η (x, y)]
    exact (integral_abs_regularizedFourierRatioKernel_slice
      (δ := δ) (x := x) hε).symm

/-- Fubini in the natural APSSS order. -/
theorem integral_fourierRatioIntegrand_prod {ε δ ξ η : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) :
    ∫ p : ℝ × ℝ, fourierRatioIntegrand ε δ ξ η p =
      ∫ x : ℝ, ∫ y : ℝ, fourierRatioIntegrand ε δ ξ η (x, y) := by
  exact integral_prod _ (integrable_fourierRatioIntegrand hε hδ)

end PSSSNative.BlockBand.PSSS
