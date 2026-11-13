module

public import Mathlib

/-!
# The semicircle Stieltjes transform off the real axis

This file defines the Stieltjes transform `m(z)` of the semicircle law used by Erdős–Riabov:
the explicit square-root formula in the upper half-plane and its Schwarz reflection in the lower
half-plane. It proves that `m` solves the Dyson equation `m² + zm + 1 = 0`, that
`Im m · Im z > 0`, and that `|m(z)| < 1` for every nonreal `z`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.External.ErdosRiabov

/-- The formula `(-z ± √(z² - 4))/2` used by ER in the upper half-plane, with the principal
square root and the sign chosen according to the sign of `Re z`. -/
def semicircleUpper (z : ℂ) : ℂ :=
  if z.re < 0 then
    (-z - Complex.sqrt (z ^ 2 - 4)) / 2
  else
    (-z + Complex.sqrt (z ^ 2 - 4)) / 2

/-- The semicircle Stieltjes transform: `semicircleUpper` in the closed upper half-plane and its
Schwarz reflection `conj (semicircleUpper (conj z))` in the lower half-plane, so that
`(Im m(z)) (Im z) > 0` for every nonreal `z`. -/
def semicircleM (z : ℂ) : ℂ :=
  if z.im < 0 then
    starRingEnd ℂ (semicircleUpper (starRingEnd ℂ z))
  else
    semicircleUpper z

/-- `m = semicircleUpper` on the closed upper half-plane. -/
theorem semicircleM_eq_upper_of_im_nonneg {z : ℂ}
    (hz : 0 ≤ z.im) :
    semicircleM z = semicircleUpper z := by
  unfold semicircleM
  split
  · rename_i h
    linarith
  · rfl

/-- `m(z) = conj (semicircleUpper (conj z))` on the open lower half-plane. -/
theorem semicircleM_eq_conj_upper_conj_of_im_neg {z : ℂ}
    (hz : z.im < 0) :
    semicircleM z =
      starRingEnd ℂ (semicircleUpper (starRingEnd ℂ z)) := by
  unfold semicircleM
  split
  · rfl
  · rename_i h
    exact False.elim (h hz)

/-- Schwarz reflection symmetry away from the real axis. -/
theorem semicircleM_conj {z : ℂ} (hz : z.im ≠ 0) :
    semicircleM (starRingEnd ℂ z) =
      starRingEnd ℂ (semicircleM z) := by
  rcases lt_or_gt_of_ne hz with hzneg | hzpos
  · rw [semicircleM_eq_conj_upper_conj_of_im_neg hzneg]
    have hconj : 0 ≤ (starRingEnd ℂ z).im := by simp; linarith
    rw [semicircleM_eq_upper_of_im_nonneg hconj]
    simp
  · rw [semicircleM_eq_upper_of_im_nonneg hzpos.le]
    have hconj : (starRingEnd ℂ z).im < 0 := by simp; linarith
    rw [semicircleM_eq_conj_upper_conj_of_im_neg hconj]
    simp

/-- The sign condition in the upper half-plane transfers to the reflected branch in the lower
half-plane. -/
theorem herglotz_sign_of_lower_reflection {z : ℂ} (hz : z.im < 0)
    (hupper : 0 <
      (semicircleUpper (starRingEnd ℂ z)).im *
        (starRingEnd ℂ z).im) :
    0 < (semicircleM z).im * z.im := by
  rw [semicircleM_eq_conj_upper_conj_of_im_neg hz]
  rw [Complex.conj_im]
  rw [Complex.conj_im] at hupper
  nlinarith

/-- In the upper half-plane the sign condition for `m` is that for `semicircleUpper`. -/
theorem herglotz_sign_of_upper {z : ℂ} (hz : 0 < z.im)
    (hupper : 0 < (semicircleUpper z).im * z.im) :
    0 < (semicircleM z).im * z.im := by
  rw [semicircleM_eq_upper_of_im_nonneg hz.le]
  exact hupper

/-- `semicircleUpper z` solves the semicircle Dyson equation `m² + zm + 1 = 0`, for either choice
of sign. -/
theorem semicircleUpper_dyson (z : ℂ) :
    semicircleUpper z ^ 2 + z * semicircleUpper z + 1 = 0 := by
  unfold semicircleUpper
  split <;> rename_i h
  · have hs : (Complex.sqrt (z ^ 2 - 4)) ^ 2 = z ^ 2 - 4 := by
      simp [Complex.sqrt]
    field_simp
    linear_combination hs
  · have hs : (Complex.sqrt (z ^ 2 - 4)) ^ 2 = z ^ 2 - 4 := by
      simp [Complex.sqrt]
    field_simp
    linear_combination hs

/-- `m` solves the Dyson equation in both half-planes. -/
theorem semicircleM_dyson (z : ℂ) :
    semicircleM z ^ 2 +
      z * semicircleM z + 1 = 0 := by
  by_cases hz : z.im < 0
  · rw [semicircleM_eq_conj_upper_conj_of_im_neg hz]
    have h := semicircleUpper_dyson (starRingEnd ℂ z)
    have hc := congrArg (starRingEnd ℂ) h
    simpa [map_add, map_mul, map_pow] using hc
  · rw [semicircleM_eq_upper_of_im_nonneg (le_of_not_gt hz)]
    exact semicircleUpper_dyson z

/-- The imaginary part of the principal square root of the semicircle
discriminant dominates the spectral height in absolute value. -/
theorem spectral_discriminant_sqrt_im_gap {z : ℂ} (hz : 0 < z.im) :
    z.im < |(Complex.sqrt (z ^ 2 - 4)).im| := by
  let d : ℂ := z ^ 2 - 4
  let R : ℝ := z.re ^ 2 + z.im ^ 2 - 4
  have hdre : d.re = z.re ^ 2 - z.im ^ 2 - 4 := by
    simp [d, pow_two]
  have hdim : d.im = 2 * z.re * z.im := by
    simp [d, pow_two]
    ring
  have hnormsq : ‖d‖ ^ 2 = R ^ 2 + 16 * z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    rw [Complex.normSq_apply]
    rw [hdre, hdim]
    simp only [R]
    ring
  have hnorm_gt : R < ‖d‖ := by
    by_cases hR : R < 0
    · exact lt_of_lt_of_le hR (norm_nonneg d)
    · have hR0 : 0 ≤ R := le_of_not_gt hR
      have hy2 : 0 < z.im ^ 2 := sq_pos_of_pos hz
      nlinarith [sq_nonneg (‖d‖ - R), norm_nonneg d]
  have hsq : z.im ^ 2 < (‖d‖ - d.re) / 2 := by
    rw [hdre]
    simp only [R] at hnorm_gt
    nlinarith
  have hrad : 0 ≤ (‖d‖ - d.re) / 2 := by
    have := Complex.re_le_norm d
    linarith
  have hsqrt_gap : z.im < Real.sqrt ((‖d‖ - d.re) / 2) := by
    exact (Real.lt_sqrt hz.le).2 hsq
  by_cases hx : 0 ≤ z.re
  · have hd_im : 0 ≤ d.im := by rw [hdim]; positivity
    have hsqrt_im :
        (Complex.sqrt d).im = Real.sqrt ((‖d‖ - d.re) / 2) := by
      simpa [Complex.sqrt] using Complex.cpow_inv_two_im_eq_sqrt hd_im
    rw [show z ^ 2 - 4 = d by rfl, hsqrt_im, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact hsqrt_gap
  · have hd_im : d.im < 0 := by
      rw [hdim]
      have hx' : z.re < 0 := lt_of_not_ge hx
      nlinarith
    have hsqrt_im :
        (Complex.sqrt d).im = -Real.sqrt ((‖d‖ - d.re) / 2) := by
      simpa [Complex.sqrt] using Complex.cpow_inv_two_im_eq_neg_sqrt hd_im
    rw [show z ^ 2 - 4 = d by rfl, hsqrt_im, abs_neg,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact hsqrt_gap

/-- `semicircleUpper` is the Herglotz root (`Im > 0`) on the open upper half-plane. -/
theorem semicircleUpper_upper_sign {z : ℂ} (hz : 0 < z.im) :
    0 < (semicircleUpper z).im * z.im := by
  have hgap := spectral_discriminant_sqrt_im_gap hz
  unfold semicircleUpper
  split <;> rename_i hx
  · have hsqrt_nonpos : (Complex.sqrt (z ^ 2 - 4)).im ≤ 0 := by
      have hd : (z ^ 2 - 4).im < 0 := by
        simp [pow_two]
        nlinarith
      rw [show Complex.sqrt (z ^ 2 - 4) =
        (z ^ 2 - 4) ^ (2⁻¹ : ℂ) by rfl,
        Complex.cpow_inv_two_im_eq_neg_sqrt hd]
      exact neg_nonpos.mpr (Real.sqrt_nonneg _)
    rw [abs_of_nonpos hsqrt_nonpos] at hgap
    simp
    nlinarith
  · have hx' : 0 ≤ z.re := le_of_not_gt hx
    have hsqrt_nonneg : 0 ≤ (Complex.sqrt (z ^ 2 - 4)).im := by
      have hd : 0 ≤ (z ^ 2 - 4).im := by
        simp [pow_two]
        nlinarith
      rw [show Complex.sqrt (z ^ 2 - 4) =
        (z ^ 2 - 4) ^ (2⁻¹ : ℂ) by rfl,
        Complex.cpow_inv_two_im_eq_sqrt hd]
      exact Real.sqrt_nonneg _
    rw [abs_of_nonneg hsqrt_nonneg] at hgap
    simp
    nlinarith

/-- `m` has the Herglotz sign `Im m · Im z > 0` on both open half-planes. -/
theorem semicircleM_same_sign {z : ℂ} (hz : z.im ≠ 0) :
    0 < (semicircleM z).im * z.im := by
  rcases lt_or_gt_of_ne hz with hzneg | hzpos
  · apply herglotz_sign_of_lower_reflection hzneg
    apply semicircleUpper_upper_sign
    simpa using neg_pos.mpr hzneg
  · exact herglotz_sign_of_upper hzpos
      (semicircleUpper_upper_sign hzpos)

/-- Pure algebraic Herglotz criterion: a solution of the semicircle Dyson equation
whose imaginary part has the sign of the spectral parameter necessarily lies strictly
inside the unit disk. -/
theorem norm_lt_one_of_dyson_and_same_sign {z m : ℂ}
    (hroot : m ^ 2 + z * m + 1 = 0)
    (hsign : 0 < m.im * z.im) : ‖m‖ < 1 := by
  have hm : m ≠ 0 := by
    intro hm
    subst m
    norm_num at hroot
  have hz : z = -(m + m⁻¹) := by
    apply (mul_right_cancel₀ hm)
    field_simp
    linear_combination hroot
  have him : z.im = m.im * (1 / Complex.normSq m - 1) := by
    rw [hz]
    simp only [Complex.neg_im, Complex.add_im, Complex.inv_im]
    field_simp [ne_of_gt (Complex.normSq_pos.mpr hm)]
    ring
  have hmim : m.im ≠ 0 := by
    intro h
    rw [h, zero_mul] at hsign
    exact (lt_irrefl 0 hsign)
  have hfactor : 0 < 1 / Complex.normSq m - 1 := by
    rw [him] at hsign
    have hsquare : 0 < m.im ^ 2 := sq_pos_of_ne_zero hmim
    nlinarith
  have hnormsq : Complex.normSq m < 1 := by
    have hsqpos : 0 < Complex.normSq m := Complex.normSq_pos.mpr hm
    have hone : 1 < (Complex.normSq m)⁻¹ := by
      rw [← one_div]
      linarith
    exact (one_lt_inv₀ hsqpos).mp hone
  rw [Complex.normSq_eq_norm_sq] at hnormsq
  nlinarith [norm_nonneg m]

/-- If `m(z)` has the Herglotz sign, then `|m(z)| < 1`. -/
theorem norm_semicircleM_lt_one_of_same_sign {z : ℂ}
    (hsign : 0 < (semicircleM z).im * z.im) :
    ‖semicircleM z‖ < 1 :=
  norm_lt_one_of_dyson_and_same_sign
    (semicircleM_dyson z) hsign

/-- `|m(z)| < 1` for every nonreal `z`. -/
theorem norm_semicircleM_lt_one {z : ℂ} (hz : z.im ≠ 0) :
    ‖semicircleM z‖ < 1 :=
  norm_semicircleM_lt_one_of_same_sign
    (semicircleM_same_sign hz)

end BlockBand.External.ErdosRiabov
