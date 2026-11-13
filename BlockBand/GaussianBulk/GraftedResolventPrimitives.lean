module
public import BlockBand.GaussianBulk.GraftedLevelRegularity
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The resolvent one-form and its logarithmic primitives

Defines the resolvent one-form `dz/(z - p)` for real `p`, computes its curve integral over a
smooth parametrized curve from a branch of the logarithm, and records the jumps of the principal
logarithm under negation that produce the winding value `2πi`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.GaussianBulk
open Set MeasureTheory
open scoped unitInterval

/-- The resolvent one-form `dz/(z - p)`. -/
def graftedResolventForm (p : ℝ) (z : ℂ) : ℂ →L[ℂ] ℂ :=
  (z-(p : ℂ))⁻¹ • ContinuousLinearMap.id ℂ ℂ

private theorem curveIntegralFun_ofLine_actual (f f' : ℝ → ℂ)
    (hf : ContinuousOn f (Icc 0 1))
    (hdf : ∀ s ∈ Icc 0 1, HasDerivAt f (f' s) s)
    (ω : ℂ → ℂ →L[ℂ] ℂ) (s : ℝ) (hs : s ∈ Icc 0 1) :
    curveIntegralFun ω (Path.ofLine hf rfl rfl) s = ω (f s) (f' s) := by
  have he : EqOn (Path.ofLine hf rfl rfl).extend f (Icc 0 1) := by
    intro t ht
    rw [Path.extend_apply _ ht]
    rfl
  rw [curveIntegralFun_def,he hs,derivWithin_congr he (he hs)]
  rw [(hdf s hs).hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc_zero_one s hs)]

/-- A curve integral over a path given by a parametrization `f` with derivative `f'` on `[0,1]`
is the integral of the real-parameter integrand. -/
theorem curveIntegral_ofLine_actual (f f' : ℝ → ℂ)
    (hf : ContinuousOn f (Icc 0 1))
    (hdf : ∀ s ∈ Icc 0 1, HasDerivAt f (f' s) s)
    (ω : ℂ → ℂ →L[ℂ] ℂ) :
    curveIntegral ω (Path.ofLine hf rfl rfl) = ∫ s in 0..1, ω (f s) (f' s) := by
  rw [curveIntegral_def]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le zero_le_one] at hs
  exact curveIntegralFun_ofLine_actual f f' hf hdf ω s hs

/-- Logarithmic primitive for a smooth parametrized curve: if `q(f(s) - p)` stays in the slit
plane, the resolvent integral is `log(q(f(1) - p)) - log(q(f(0) - p))`. In applications `q = 1`
on the upper, lower and right pieces and `q = -1` on the left connector. -/
theorem curveIntegral_ofLine_resolvent_log (f f' : ℝ → ℂ) (p : ℝ) (q : ℂ)
    (hq : q ≠ 0) (hf : ContinuousOn f (Icc 0 1))
    (hdf : ∀ s ∈ Icc 0 1, HasDerivAt f (f' s) s)
    (hdf' : ContinuousOn f' (Icc 0 1))
    (hslit : ∀ s ∈ Icc 0 1, q*(f s-(p : ℂ)) ∈ Complex.slitPlane) :
    CurveIntegrable (graftedResolventForm p) (Path.ofLine hf rfl rfl) ∧
      curveIntegral (graftedResolventForm p) (Path.ofLine hf rfl rfl) =
        Complex.log (q*(f 1-(p : ℂ)))-Complex.log (q*(f 0-(p : ℂ))) := by
  have hne (s : ℝ) (hs : s ∈ Icc 0 1) : f s-(p : ℂ) ≠ 0 := by
    have hn := Complex.slitPlane_ne_zero (hslit s hs)
    exact fun he => hn (by rw [he,mul_zero])
  have hint : IntervalIntegrable (fun s => f' s/(f s-(p : ℂ))) volume 0 1 :=
    (hdf'.div (hf.sub continuousOn_const) hne).intervalIntegrable_of_Icc zero_le_one
  have hlog (s : ℝ) (hs : s ∈ Icc 0 1) :
      HasDerivAt (fun s => Complex.log (q*(f s-(p : ℂ))))
        (f' s/(f s-(p : ℂ))) s := by
    have hd := (((hdf s hs).sub_const (p : ℂ)).const_mul q).clog_real (hslit s hs)
    simpa only [mul_div_mul_left _ _ hq] using hd
  have hform (s : ℝ) : graftedResolventForm p (f s) (f' s) = f' s/(f s-(p : ℂ)) := by
    simp only [graftedResolventForm,smul_apply,
      ContinuousLinearMap.id_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]
  constructor
  · unfold CurveIntegrable
    apply (intervalIntegrable_congr (f := curveIntegralFun (graftedResolventForm p)
      (Path.ofLine hf rfl rfl)) (g := fun s => f' s/(f s-(p : ℂ))) ?_).mpr hint
    intro s hs
    rw [uIoc_of_le zero_le_one] at hs
    rw [curveIntegralFun_ofLine_actual f f' hf hdf _ s ⟨hs.1.le,hs.2⟩,hform]
  · rw [curveIntegral_ofLine_actual f f' hf hdf]
    simp_rw [hform]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs => hlog s (by simpa only [uIcc_of_le zero_le_one] using hs)) hint

/-- The principal logarithm of `-w` for `w` in the upper half-plane. -/
theorem graftedLog_neg_of_im_pos (w : ℂ) (hw : 0 < w.im) :
    Complex.log (-w) = Complex.log w-(Real.pi : ℂ)*Complex.I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp only [Complex.log_im,Complex.sub_im,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero]
    exact Complex.arg_neg_eq_arg_sub_pi_of_im_pos hw

/-- The principal logarithm of `-w` for `w` in the lower half-plane. -/
theorem graftedLog_neg_of_im_neg (w : ℂ) (hw : w.im < 0) :
    Complex.log (-w) = Complex.log w+(Real.pi : ℂ)*Complex.I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp only [Complex.log_im,Complex.add_im,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero]
    exact Complex.arg_neg_eq_arg_add_pi_of_im_neg hw

/-- For `Im w > 0`: `log w - log w̄ + log(-w̄) - log(-w) = 2πi`. The four branch values at the
corners of a positively oriented reflected loop telescope to the winding value. -/
theorem graftedResolventLog_jump (w : ℂ) (hw : 0 < w.im) :
    Complex.log w-Complex.log (star w)+Complex.log (-star w)-Complex.log (-w) =
      2*(Real.pi : ℂ)*Complex.I := by
  have hc : (star w).im < 0 := by
    simp only [Complex.star_def,Complex.conj_im]
    linarith
  rw [graftedLog_neg_of_im_pos w hw,graftedLog_neg_of_im_neg (star w) hc]
  ring

end BlockBand.GaussianBulk
