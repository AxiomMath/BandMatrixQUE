module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Elementary kernel inequalities for the Herglotz tail lemma

* `norm_inv_sub_I_sub_inv_le` — the displayed inequality of the tightness step:
  for real `x` with `|x| ≥ a > 0`, `|1/(x-i) - 1/x| ≤ √(1+a⁻²)/(x²+1)`.
* `norm_inv_sub_sub_inv_le` — far-variation kernel: for real `y` with `|y| ≥ 1` and
  `|y| ≥ 2|z|`, `|1/(y-z) - 1/y| ≤ 4|z|/(1+y²)` (used to compare a far spectral tail at `z`
  with its value at the real base point `0`).
* `norm_cexp_I_mul_le_one`, `norm_cexp_I_mul_sub_le` — on the closed upper half-plane and for
  `t ≥ 0`, `|e^{itw}| ≤ 1` and `|e^{itw} - e^{itw'}| ≤ t|w-w'|` (the bounded analytic mean step).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Complex

namespace BlockBand.Critical.Herglotz

/-- **Kernel inequality of the tightness step.**
Domain: `x : ℝ`, `a > 0`, `a ≤ |x|`. Norm: complex modulus. Conclusion:
`‖(x - i)⁻¹ - x⁻¹‖ ≤ √(1 + a⁻²) / (x² + 1)`. -/
theorem norm_inv_sub_I_sub_inv_le {a x : ℝ} (ha : 0 < a) (hx : a ≤ |x|) :
    ‖((x : ℂ) - I)⁻¹ - (x : ℂ)⁻¹‖ ≤ Real.sqrt (1 + a⁻¹ ^ 2) / (x ^ 2 + 1) := by
  have hx0 : x ≠ 0 := by
    intro h; rw [h, abs_zero] at hx; linarith
  have hxI : (x : ℂ) - I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx0
  have hid : ((x : ℂ) - I)⁻¹ - (x : ℂ)⁻¹ = I / (((x : ℂ) - I) * x) := by
    field_simp
    ring
  have hnI : ‖(x : ℂ) - I‖ = Real.sqrt (x ^ 2 + 1) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    congr 1
    simp
    ring
  rw [hid, norm_div, norm_mul, Complex.norm_I, hnI, Complex.norm_real, Real.norm_eq_abs]
  have hx2 : 0 < x ^ 2 + 1 := by positivity
  have hsq : 0 < Real.sqrt (x ^ 2 + 1) := Real.sqrt_pos.mpr hx2
  have habs : 0 < |x| := abs_pos.mpr hx0
  rw [div_le_div_iff₀ (mul_pos hsq habs) hx2, one_mul]
  -- `x² + 1 = √(x²+1)²` and `√(x²+1) ≤ √(1+a⁻²) |x|`.
  have hkey : Real.sqrt (x ^ 2 + 1) ≤ Real.sqrt (1 + a⁻¹ ^ 2) * |x| := by
    rw [← Real.sqrt_sq habs.le, ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    have h1 : a ^ 2 ≤ |x| ^ 2 := by
      exact pow_le_pow_left₀ ha.le hx 2
    have h2 : (1 : ℝ) ≤ a⁻¹ ^ 2 * |x| ^ 2 := by
      rw [inv_pow, inv_mul_eq_div, le_div_iff₀ (by positivity), one_mul]
      exact h1
    rw [sq_abs] at h2 ⊢
    nlinarith
  have hsq2 : Real.sqrt (x ^ 2 + 1) * Real.sqrt (x ^ 2 + 1) = x ^ 2 + 1 :=
    Real.mul_self_sqrt hx2.le
  nlinarith [hsq2, hkey, hsq.le]

/-- **Far-variation kernel.** Domain: `y : ℝ`, `z : ℂ` with `1 ≤ |y|` and `2‖z‖ ≤ |y|`.
Conclusion: `‖(y - z)⁻¹ - y⁻¹‖ ≤ 4‖z‖/(1 + y²)`. -/
theorem norm_inv_sub_sub_inv_le {y : ℝ} {z : ℂ} (hy : 1 ≤ |y|) (hz : 2 * ‖z‖ ≤ |y|) :
    ‖((y : ℂ) - z)⁻¹ - (y : ℂ)⁻¹‖ ≤ 4 * ‖z‖ / (1 + y ^ 2) := by
  have hy0 : 0 < |y| := by linarith
  have hyC : (y : ℂ) ≠ 0 := by
    have : y ≠ 0 := abs_pos.mp hy0
    exact_mod_cast this
  have hyz : ‖(y : ℂ) - z‖ ≥ |y| / 2 := by
    have := norm_sub_norm_le (y : ℂ) z
    rw [Complex.norm_real, Real.norm_eq_abs] at this
    linarith
  have hyz0 : (y : ℂ) - z ≠ 0 := by
    intro h; rw [h, norm_zero] at hyz; linarith
  have hid : ((y : ℂ) - z)⁻¹ - (y : ℂ)⁻¹ = z / (((y : ℂ) - z) * y) := by
    field_simp
    ring
  rw [hid, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hden : 0 < ‖(y : ℂ) - z‖ * |y| := by
    have : 0 < ‖(y : ℂ) - z‖ := by linarith
    positivity
  rw [div_le_div_iff₀ hden (by positivity)]
  have hy2 : |y| ^ 2 = y ^ 2 := sq_abs y
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  -- `‖z‖ (1 + y²) ≤ 2 ‖z‖ y² ≤ 4 ‖z‖ ‖y - z‖ |y|`.
  have h1 : 1 + y ^ 2 ≤ 2 * y ^ 2 := by nlinarith
  have h2 : y ^ 2 ≤ 2 * (‖(y : ℂ) - z‖ * |y|) := by nlinarith
  nlinarith

/-- `|e^{itw}| ≤ 1` for `t ≥ 0` and `0 ≤ Im w`. -/
theorem norm_cexp_I_mul_le_one {t : ℝ} (ht : 0 ≤ t) {w : ℂ} (hw : 0 ≤ w.im) :
    ‖cexp (I * t * w)‖ ≤ 1 := by
  rw [Complex.norm_exp]
  have : (I * t * w).re = -(t * w.im) := by simp
  rw [this, Real.exp_le_one_iff]
  nlinarith

/-- **Lipschitz bound for bounded analytic exponentials** (the bounded analytic mean step).
Domain: `t ≥ 0`, `w, w'` in the closed upper half-plane. Conclusion:
`‖e^{itw} - e^{itw'}‖ ≤ t ‖w - w'‖`. -/
theorem norm_cexp_I_mul_sub_le {t : ℝ} (ht : 0 ≤ t) {w w' : ℂ} (hw : 0 ≤ w.im)
    (hw' : 0 ≤ w'.im) :
    ‖cexp (I * t * w) - cexp (I * t * w')‖ ≤ t * ‖w - w'‖ := by
  let s : Set ℂ := {ζ | 0 ≤ ζ.im}
  have hs : Convex ℝ s := by
    intro a ha b hb μ ν hμ hν _
    simp only [s, Set.mem_ofPred_eq, Complex.add_im, Complex.smul_im] at ha hb ⊢
    positivity
  have hderiv : ∀ ζ ∈ s, HasDerivWithinAt (fun ζ => cexp (I * t * ζ))
      (cexp (I * t * ζ) * (I * t)) s ζ := by
    intro ζ _
    have h := ((hasDerivAt_id ζ).const_mul (I * t)).cexp
    simp only [mul_one, id] at h
    exact h.hasDerivWithinAt
  have hbound : ∀ ζ ∈ s, ‖cexp (I * t * ζ) * (I * t)‖ ≤ t := by
    intro ζ hζ
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht]
    have := norm_cexp_I_mul_le_one ht (w := ζ) hζ
    nlinarith
  have := hs.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound hw' hw
  simpa using this

end BlockBand.Critical.Herglotz
