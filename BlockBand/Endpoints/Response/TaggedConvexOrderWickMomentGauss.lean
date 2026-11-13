module

public import BlockBand.Endpoints.Response.TaggedConvexOrderGaussian
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Probability.ProductMeasure

/-!
# Moments of the standard circular Gaussian vector

Law: `h ~ circularVectorLaw ι` (`CoareaPalm`): `h_a = r_{a,0} + i r_{a,1}` with
`r ~ Π_{ι × Fin 2} N(0, 1/2)`, so `E|h_a|² = 1`.

* `wk_integral_c2_normSq_pow`: one coordinate, `E|g|^{2k} = k!` (polar coordinates on `ℂ`,
  `integral_fun_norm_addHaar`, and `∫_0^∞ r^{2k+1} e^{-r²} dr = k!/2`).
* `wk_integral_prod_normSq_pow`: independence of the coordinates,
  `E Π_a |h_a|^{2 k_a} = Π_a k_a!` for every `k : ι → ℕ` (uniform in `ι`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Real Set Metric
open BlockBand.Internal.Contracts.CoareaPalm
open scoped ENNReal NNReal

/-- One circular coordinate from its two real parts. -/
def wk_c2 (t : Fin 2 → ℝ) : ℂ := (t 0 : ℂ) + (t 1 : ℂ) * Complex.I

theorem wk_gaussianPDFReal_half (x : ℝ) :
    gaussianPDFReal 0 (1 / 2 : ℝ≥0) x = (√π)⁻¹ * exp (-x ^ 2) := by
  simp only [gaussianPDFReal, sub_zero]
  congr 2
  · push_cast; ring_nf
  · push_cast; ring

/-- `∫_0^∞ r^{2k+1} e^{-r²} dr = k!/2`. -/
theorem wk_radial_moment (k : ℕ) :
    ∫ y in Ioi (0 : ℝ), y ^ (2 * k + 1) * exp (-y ^ 2) = k.factorial / 2 := by
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  have h := integral_rpow_mul_exp_neg_rpow (p := 2) (q := (2 * k + 1 : ℝ)) two_pos (by linarith)
  have hc : ∫ y in Ioi (0 : ℝ), y ^ (2 * k + 1) * exp (-y ^ 2) =
      ∫ y in Ioi (0 : ℝ), y ^ (2 * k + 1 : ℝ) * exp (-y ^ (2 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    have e1 : y ^ (2 * k + 1 : ℝ) = y ^ (2 * k + 1) := by
      exact_mod_cast Real.rpow_natCast y (2 * k + 1)
    simp only [e1, Real.rpow_two]
  rw [hc, h, show ((2 * k + 1 : ℝ) + 1) / 2 = (k : ℝ) + 1 by ring, Real.Gamma_nat_eq_factorial]
  ring

/-- **One circular coordinate:** `E|g|^{2k} = k!` for `g = x + iy`, `x, y ~ N(0, 1/2)`. -/
theorem wk_integral_c2_normSq_pow (k : ℕ) :
    ∫ t, Complex.normSq (wk_c2 t) ^ k
        ∂(Measure.pi fun _ : Fin 2 => gaussianReal 0 (1 / 2 : ℝ≥0)) = k.factorial := by
  set γ := gaussianReal 0 (1 / 2 : ℝ≥0)
  have hv : (1 / 2 : ℝ≥0) ≠ 0 := by norm_num
  set K : ℝ × ℝ → ℝ := fun p => (p.1 ^ 2 + p.2 ^ 2) ^ k
  have h1 : ∫ t, Complex.normSq (wk_c2 t) ^ k ∂(Measure.pi fun _ : Fin 2 => γ) =
      ∫ p, K p ∂(γ.prod γ) := by
    rw [← (measurePreserving_finTwoArrow γ).integral_comp' K]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp [K, wk_c2, Complex.normSq_apply, MeasurableEquiv.finTwoArrow, pow_two]
  have h2 : γ.prod γ = (volume : Measure (ℝ × ℝ)).withDensity
      (fun z => gaussianPDF 0 (1 / 2 : ℝ≥0) z.1 * gaussianPDF 0 (1 / 2 : ℝ≥0) z.2) := by
    simp only [γ]
    rw [gaussianReal_of_var_ne_zero 0 hv,
      prod_withDensity (measurable_gaussianPDF _ _) (measurable_gaussianPDF _ _)]
    rfl
  have hmeas : Measurable
      (fun z : ℝ × ℝ => gaussianPDF 0 (1 / 2 : ℝ≥0) z.1 * gaussianPDF 0 (1 / 2 : ℝ≥0) z.2) :=
    ((measurable_gaussianPDF _ _).comp measurable_fst).mul
      ((measurable_gaussianPDF _ _).comp measurable_snd)
  have hfin : ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
      gaussianPDF 0 (1 / 2 : ℝ≥0) z.1 * gaussianPDF 0 (1 / 2 : ℝ≥0) z.2 < ∞ :=
    ae_of_all _ fun z => ENNReal.mul_lt_top (by simp [gaussianPDF]) (by simp [gaussianPDF])
  set f : ℝ → ℝ := fun r => π⁻¹ * (exp (-r ^ 2) * (r ^ 2) ^ k)
  have h3 : ∫ p, K p ∂(γ.prod γ) = ∫ z : ℂ, f ‖z‖ := by
    rw [h2, integral_withDensity_eq_integral_toReal_smul hmeas hfin,
      ← Complex.volume_preserving_equiv_real_prod.integral_comp']
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    have he : Complex.measurableEquivRealProd z = (z.re, z.im) := rfl
    simp only [he, ENNReal.toReal_mul, toReal_gaussianPDF,
      wk_gaussianPDFReal_half, smul_eq_mul, K, f]
    have hn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [hn]
    have hpi : (√π)⁻¹ * (√π)⁻¹ = π⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt pi_pos.le]
    rw [show -(z.re ^ 2 + z.im ^ 2) = -z.re ^ 2 + -z.im ^ 2 by ring, Real.exp_add, ← hpi]
    ring
  have hball : (volume : Measure ℂ).real (ball 0 1) = π := by
    simp [Measure.real, Complex.volume_ball]
  rw [h1, h3, integral_fun_norm_addHaar volume f, Complex.finrank_real_complex, hball]
  have h4 : ∫ y in Ioi (0 : ℝ), y ^ (2 - 1) • f y =
      π⁻¹ * ∫ y in Ioi (0 : ℝ), y ^ (2 * k + 1) * exp (-y ^ 2) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    simp only [f, smul_eq_mul]
    ring
  rw [h4, wk_radial_moment]
  have := pi_pos.ne'
  simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat]
  field_simp

/-- `Π_{ι × Fin 2} γ` is the image of `Π_ι Π_{Fin 2} γ` under uncurrying. -/
theorem wk_pi_prod_eq_map_uncurry (ι : Type) [Fintype ι] :
    (Measure.pi fun _ : ι × Fin 2 => gaussianReal 0 (1 / 2 : ℝ≥0)) =
      (Measure.pi fun _ : ι => Measure.pi fun _ : Fin 2 => gaussianReal 0 (1 / 2 : ℝ≥0)).map
        (MeasurableEquiv.curry ι (Fin 2) ℝ).symm := by
  have h := Measure.infinitePi_map_curry_symm (fun (_ : ι) (_ : Fin 2) => gaussianReal 0 (1 / 2 : ℝ≥0))
  simp only [Measure.infinitePi_eq_pi] at h
  exact h.symm

/-- **Independent coordinates:** `E Π_a |h_a|^{2 k_a} = Π_a k_a!` for `h ~ circularVectorLaw ι`. -/
theorem wk_integral_prod_normSq_pow {ι : Type} [Fintype ι] (k : ι → ℕ) :
    ∫ h, ∏ a, Complex.normSq (h a) ^ k a ∂circularVectorLaw ι = ∏ a, ((k a).factorial : ℝ) := by
  have hF : Continuous fun h : ι → ℂ => ∏ a, Complex.normSq (h a) ^ k a :=
    continuous_finsetProd _ fun a _ => (Complex.continuous_normSq.comp (continuous_apply a)).pow _
  unfold circularVectorLaw
  rw [integral_map (by fun_prop) hF.aestronglyMeasurable, wk_pi_prod_eq_map_uncurry,
    integral_map_equiv]
  have hc : ∀ s : ι → Fin 2 → ℝ,
      (∏ a, Complex.normSq (((MeasurableEquiv.curry ι (Fin 2) ℝ).symm s (a, 0) : ℂ) +
        ((MeasurableEquiv.curry ι (Fin 2) ℝ).symm s (a, 1) : ℂ) * Complex.I) ^ k a) =
        ∏ a, (fun (a : ι) (t : Fin 2 → ℝ) => Complex.normSq (wk_c2 t) ^ k a) a (s a) := by
    intro s
    rfl
  simp_rw [hc]
  refine (integral_fintype_prod_eq_prod (fun (a : ι) (t : Fin 2 → ℝ) =>
    Complex.normSq (wk_c2 t) ^ k a)).trans ?_
  exact Finset.prod_congr rfl fun a _ => wk_integral_c2_normSq_pow (k a)

end BlockBand.Endpoints
